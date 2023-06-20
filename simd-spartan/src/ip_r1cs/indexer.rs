use crate::dense_mle::merge_dense_mle;
use crate::Error;

use super::IPForR1CS;
use ark_ff::PrimeField;
use ark_poly::DenseMultilinearExtension;
use ark_relations::lc;
use ark_relations::r1cs::{
    ConstraintMatrices, ConstraintSynthesizer, ConstraintSystem, ConstraintSystemRef,
    OptimizationGoal, SynthesisMode,
};
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize, SerializationError};
use ark_sponge::{
    collect_sponge_bytes, collect_sponge_field_elements, Absorb, CryptographicSponge,
};
use ark_std::{end_timer, start_timer};
use ark_std::{
    io::{Read, Write},
    marker::PhantomData,
};
use derivative::Derivative;

pub(crate) fn balance_matrices<F: PrimeField>(a_matrix: &mut Matrix<F>, b_matrix: &mut Matrix<F>) {
    let mut a_density: usize = a_matrix.iter().map(|row| row.len()).sum();
    let mut b_density: usize = b_matrix.iter().map(|row| row.len()).sum();
    let mut max_density = core::cmp::max(a_density, b_density);
    let mut a_is_denser = a_density == max_density;
    for (a_row, b_row) in a_matrix.iter_mut().zip(b_matrix) {
        if a_is_denser {
            let a_row_size = a_row.len();
            let b_row_size = b_row.len();
            core::mem::swap(a_row, b_row);
            a_density = a_density - a_row_size + b_row_size;
            b_density = b_density - b_row_size + a_row_size;
            max_density = core::cmp::max(a_density, b_density);
            a_is_denser = a_density == max_density;
        }
    }
}

pub(crate) fn max_weight<F: PrimeField>(a: &Matrix<F>, b: &Matrix<F>, c: &Matrix<F>) -> usize {
    let a_num_non_zero: usize = a.iter().map(|lc| lc.len()).sum();
    let b_num_non_zero: usize = b.iter().map(|lc| lc.len()).sum();
    let c_num_non_zero: usize = c.iter().map(|lc| lc.len()).sum();
    let max_weight = *[a_num_non_zero, b_num_non_zero, c_num_non_zero]
        .iter()
        .max()
        .unwrap();
    max_weight
}

pub(crate) fn make_matrices_square<F: PrimeField>(cs: ConstraintSystemRef<F>) {
    // println!("Within make_matrices_square inputs: {}", cs.num_instance_variables());
    // println!("Within make_matrices_square witnesses: {}", cs.num_witness_variables());
    let num_variables = cs.num_instance_variables() + cs.num_witness_variables();
    let num_constraints = cs.num_constraints();
    assert!(
        num_variables.is_power_of_two(),
        "num_variables must be a power of two for this implementation"
    );
    let matrix_padding = ((num_variables as isize) - (num_constraints as isize)).abs();
    if num_variables >= num_constraints {
        for _ in 0..matrix_padding {
            cs.enforce_constraint(lc!(), lc!(), lc!())
                .expect("enforce 0 * 0 == 0 failed");
        }
    } else {
        assert!(
            false,
            "this should not be happening with current padding implementation"
        );
        // Add dummy unconstrained variables
        for _ in 0..matrix_padding {
            let _ = cs
                .new_witness_variable(|| Ok(F::one()))
                .expect("alloc failed");
        }
    }
    // println!(
    //     "num_variables: {}",
    //     cs.num_instance_variables() + cs.num_witness_variables()
    // );
    // println!("num_constraints: {}", cs.num_constraints());
    assert_eq!(
        cs.num_instance_variables() + cs.num_witness_variables(),
        cs.num_constraints(),
        "padding failed!"
    );
    assert!(
        cs.num_constraints().is_power_of_two(),
        "padding does not result in expected matrix size!"
    );
}

/// make num_input_instances and num_vars a power of 2
pub(crate) fn pad_variables<F: PrimeField>(cs: ConstraintSystemRef<F>) {
    // println!("Before padding inputs: {}", cs.num_instance_variables());
    // println!("Before padding witnesses: {}", cs.num_witness_variables());
    let input_size = cs.num_instance_variables();
    let witness_size = cs.num_witness_variables();
    let var_size = input_size + witness_size;

    assert!(input_size <= witness_size, "inputs > witness");

    let mut padded_witness_size = witness_size.next_power_of_two();
    while 2 * padded_witness_size < cs.num_constraints() {
        padded_witness_size *= 2;
    }
    // TODO: fix
    // for now, setting #inputs = #witnesses = power of 2
    let padded_input_size = padded_witness_size;
    let input_padding = padded_input_size - input_size;
    let padded_var_size = padded_input_size + padded_witness_size;
    let witness_padding = padded_var_size - var_size - input_padding;

    for _ in 0..input_padding {
        cs.new_input_variable(|| Ok(F::zero()))
            .expect("alloc input failed");
    }
    for _ in 0..witness_padding {
        cs.new_witness_variable(|| Ok(F::one()))
            .expect("alloc witness failed");
    }
    // println!("After padding inputs: {}", cs.num_instance_variables());
    // println!("After padding witnesses: {}", cs.num_witness_variables());
}

/// Information about the index, including the field of definition, the number of
/// variables, the number of constraints, and the maximum number of non-zero
/// entries in any of the constraint matrices.
#[derive(Derivative, CanonicalSerialize, CanonicalDeserialize, Debug)]
#[derivative(Clone(bound = ""), Copy(bound = ""))]
pub struct IndexInfo<F> {
    /// The number of data-parallel instances
    pub num_copies: usize,
    /// The total number of variables in the constraint system.
    pub num_variables: usize,
    /// The number of constraints.
    pub num_constraints: usize,
    /// The maximum number of non-zero entries in any constraint matrix.
    pub max_weight: usize,
    /// The number of input elements.
    pub num_instance_variables: usize,

    #[doc(hidden)]
    pub f: PhantomData<F>,
}

impl<F: PrimeField> Absorb for IndexInfo<F> {
    fn to_sponge_bytes(&self, dest: &mut Vec<u8>) {
        let tmp = collect_sponge_bytes!(
            self.num_copies,
            self.num_variables,
            self.num_constraints,
            self.max_weight,
            self.num_instance_variables
        );
        dest.extend(tmp);
    }

    fn to_sponge_field_elements<CF: PrimeField>(&self, dest: &mut Vec<CF>) {
        let tmp: Vec<CF> = collect_sponge_field_elements!(
            self.num_copies.to_le_bytes().to_vec(),
            self.num_variables.to_le_bytes().to_vec(),
            self.num_constraints.to_le_bytes().to_vec(),
            self.max_weight.to_le_bytes().to_vec(),
            self.num_instance_variables.to_le_bytes().to_vec()
        );
        dest.extend(tmp);
    }
}

impl<F: PrimeField> IndexInfo<F> {
    /// The maximum number of variables of any polynomial in this index
    pub fn max_nv(&self) -> usize {
        std::cmp::max(
            self.constraints_nv() + std::cmp::max(4, self.copies_nv()),
            self.weight_nv() + 3,
        )
    }

    pub fn copies_nv(&self) -> usize {
        self.num_copies.next_power_of_two().trailing_zeros() as usize
    }

    pub fn input_nv(&self) -> usize {
        self.num_instance_variables
            .next_power_of_two()
            .trailing_zeros() as usize
    }

    pub fn constraints_nv(&self) -> usize {
        self.num_constraints.next_power_of_two().trailing_zeros() as usize
    }

    pub fn weight_nv(&self) -> usize {
        self.max_weight.next_power_of_two().trailing_zeros() as usize
    }

    pub fn batch_weight_poly_nv(&self) -> usize {
        4
    }

    pub fn batch_constraints_poly_nv(&self) -> usize {
        3
    }
}

impl<F: PrimeField> ark_ff::ToBytes for IndexInfo<F> {
    fn write<W: Write>(&self, mut w: W) -> ark_std::io::Result<()> {
        (self.num_variables as u64).write(&mut w)?;
        (self.num_constraints as u64).write(&mut w)?;
        (self.max_weight as u64).write(&mut w)
    }
}

/// Represents a matrix.
pub type Matrix<F> = Vec<Vec<(F, usize)>>;

/// Contains information about the arithmetization of the matrix M.
#[derive(Derivative, CanonicalSerialize, CanonicalDeserialize)]
#[derivative(Clone(bound = "F: PrimeField"))]
pub struct MatrixArithmetization<F: PrimeField> {
    /// (padded to power of 2) row indices
    pub row: Vec<usize>,
    /// (padded to power of 2) col indices
    pub col: Vec<usize>,
    /// MLE of row indices
    pub row_mle: DenseMultilinearExtension<F>,
    /// MLE of col indices
    pub col_mle: DenseMultilinearExtension<F>,
    /// MLE of the non-zero entries
    pub val_mle: DenseMultilinearExtension<F>,
    /// MLE of row_read
    pub row_read_mle: DenseMultilinearExtension<F>,
    /// MLE of row_final
    pub row_final_mle: DenseMultilinearExtension<F>,
    /// MLE of col_read
    pub col_read_mle: DenseMultilinearExtension<F>,
    /// MLE of col_final
    pub col_final_mle: DenseMultilinearExtension<F>,
}

pub(crate) fn arithmetize_matrix<F: PrimeField>(
    matrix: &mut Matrix<F>,
    // weight < 1 << m
    m: usize,
    // constraints < 1 << n
    n: usize,
) -> MatrixArithmetization<F> {
    let matrix_time = start_timer!(|| "Computing row, col, and val MLEs");

    let mut row_vec = Vec::new();
    let mut col_vec = Vec::new();
    let mut val_mle_vec = Vec::new();
    let mut row_read_mle_vec = vec![0; 1 << m];
    let mut row_final_mle_vec = vec![0; 1 << n];
    let mut col_read_mle_vec = vec![0; 1 << m];
    let mut col_final_mle_vec = vec![0; 1 << n];

    let mut count = 0;
    let mut row_ts = 0;
    let mut col_ts = 0;
    let matrix_weight: usize = matrix.iter().map(|lc| lc.len()).sum();
    let final_row_idx = matrix.len() - 1;
    let final_row = &matrix[final_row_idx];
    let (final_val, final_col_idx) = if final_row.len() == 0 {
        (F::zero(), 0)
    } else {
        final_row[final_row.len() - 1]
    };

    for (r, row) in matrix.into_iter().enumerate() {
        if !is_in_ascending_order(&row, |(_, a), (_, b)| a < b) {
            row.sort_by(|(_, a), (_, b)| a.cmp(b));
        };
        if r == final_row_idx {
            // pad the final row to pad weight to 1 << m
            let padding = vec![(final_val, final_col_idx); (1 << m) - matrix_weight];
            row.extend(padding);
        }

        for &mut (val, i) in row {
            let row_val = r;
            let col_val = i;
            row_vec.push(row_val);
            col_vec.push(col_val);
            val_mle_vec.push(val);

            let row_r_ts = row_final_mle_vec[row_val];
            let col_r_ts = col_final_mle_vec[col_val];
            // since read timestamps are trustworthy, we can simply increment the r_ts to obtain ts
            row_ts = row_r_ts + 1;
            col_ts = col_r_ts + 1;
            // row_ts = std::cmp::max(row_ts, row_r_ts) + 1;
            // col_ts = std::cmp::max(col_ts, col_r_ts) + 1;
            row_read_mle_vec[count] = row_r_ts;
            row_final_mle_vec[row_val] = row_ts;
            col_read_mle_vec[count] = col_r_ts;
            col_final_mle_vec[col_val] = col_ts;

            count += 1;
        }
    }
    assert!(count == (1 << m));
    end_timer!(matrix_time);

    let to_dense_mle = |vec: &Vec<usize>, nv: usize| {
        DenseMultilinearExtension::from_evaluations_vec(
            nv,
            vec.iter().map(|&x| F::from(x as u64)).collect(),
        )
    };

    MatrixArithmetization {
        row_mle: to_dense_mle(&row_vec, m),
        col_mle: to_dense_mle(&col_vec, m),
        row: row_vec,
        col: col_vec,
        val_mle: DenseMultilinearExtension {
            evaluations: val_mle_vec,
            num_vars: m,
        },
        row_read_mle: to_dense_mle(&row_read_mle_vec, m),
        row_final_mle: to_dense_mle(&row_final_mle_vec, n),
        col_read_mle: to_dense_mle(&col_read_mle_vec, m),
        col_final_mle: to_dense_mle(&col_final_mle_vec, n),
    }
}

fn is_in_ascending_order<T: Ord>(x_s: &[T], is_less_than: impl Fn(&T, &T) -> bool) -> bool {
    if x_s.is_empty() {
        true
    } else {
        let mut i = 0;
        let mut is_sorted = true;
        while i < (x_s.len() - 1) {
            is_sorted &= is_less_than(&x_s[i], &x_s[i + 1]);
            i += 1;
        }
        is_sorted
    }
}

#[derive(Derivative)]
#[derivative(Clone(bound = "F: PrimeField"))]
#[derive(CanonicalSerialize, CanonicalDeserialize)]
pub struct Index<F: PrimeField> {
    /// Information about the index.
    pub index_info: IndexInfo<F>,

    /// The A matrix for the R1CS instance
    pub a: Matrix<F>,
    /// The B matrix for the R1CS instance
    pub b: Matrix<F>,
    /// The C matrix for the R1CS instance
    pub c: Matrix<F>,

    /// Arithmetization of the A* matrix.
    pub a_arith: MatrixArithmetization<F>,
    /// Arithmetization of the B* matrix.
    pub b_arith: MatrixArithmetization<F>,
    /// Arithmetization of the C* matrix.
    pub c_arith: MatrixArithmetization<F>,
}

impl<F: PrimeField> Index<F> {
    pub fn merged_r_m_poly(&self) -> DenseMultilinearExtension<F> {
        let mle_vec = ark_std::vec![
            &self.a_arith.val_mle,
            &self.b_arith.val_mle,
            &self.c_arith.val_mle,
            &self.a_arith.row_mle,
            &self.b_arith.row_mle,
            &self.c_arith.row_mle,
            &self.a_arith.col_mle,
            &self.b_arith.col_mle,
            &self.c_arith.col_mle,
            &self.a_arith.row_read_mle,
            &self.b_arith.row_read_mle,
            &self.c_arith.row_read_mle,
            &self.a_arith.col_read_mle,
            &self.b_arith.col_read_mle,
            &self.c_arith.col_read_mle,
        ];
        merge_dense_mle(mle_vec)
    }

    pub fn merged_r_n_poly(&self) -> DenseMultilinearExtension<F> {
        let mle_vec = ark_std::vec![
            &self.a_arith.row_final_mle,
            &self.b_arith.row_final_mle,
            &self.c_arith.row_final_mle,
            &self.a_arith.col_final_mle,
            &self.b_arith.col_final_mle,
            &self.c_arith.col_final_mle,
        ];
        merge_dense_mle(mle_vec)
    }
}

impl<F: PrimeField, S: CryptographicSponge> IPForR1CS<F, S> {
    /// Generate the index for this constraint system.
    pub fn index<C: ConstraintSynthesizer<F>>(num_copies: usize, c: C) -> Result<Index<F>, Error> {
        let index_time = start_timer!(|| "Index");

        let constraint_time = start_timer!(|| "Generating constraints");
        let ics = ConstraintSystem::new_ref();
        // ics.set_optimization_goal(OptimizationGoal::Weight);
        ics.set_optimization_goal(OptimizationGoal::Constraints);
        ics.set_mode(SynthesisMode::Setup);
        c.generate_constraints(ics.clone())?;
        end_timer!(constraint_time);
        // before padding
        let num_input_variables = ics.num_instance_variables();

        let matrix_processing_time = start_timer!(|| "Processing matrices");
        ics.finalize();
        let padding_time = start_timer!(|| "Padding matrices to make them square");
        pad_variables(ics.clone());
        end_timer!(padding_time);
        make_matrices_square(ics.clone());
        let matrices = ics.to_matrices().expect("should not be `None`");
        let (mut a, mut b, mut c) = (matrices.a, matrices.b, matrices.c);
        balance_matrices(&mut a, &mut b);
        let max_weight = max_weight::<F>(&a, &b, &c);
        // println!("max_weight: {}", max_weight);
        end_timer!(matrix_processing_time);

        let (padded_num_input_variables, num_witness_variables, num_constraints, max_weight) = (
            ics.num_instance_variables(),
            ics.num_witness_variables(),
            ics.num_constraints(),
            max_weight,
        );
        let num_variables = padded_num_input_variables + num_witness_variables;

        if num_constraints != padded_num_input_variables + num_witness_variables {
            eprintln!(
                "number of formatted_input_variables: {}",
                padded_num_input_variables
            );
            eprintln!("number of witness_variables: {}", num_witness_variables);
            eprintln!("number of num_constraints: {}", num_constraints);
            eprintln!("number of num_non_zero: {}", max_weight);
            return Err(Error::NonSquareMatrix);
        }
        if !padded_num_input_variables.is_power_of_two() {
            return Err(Error::InvalidPublicInputLength);
        }
        if !num_constraints.is_power_of_two() {
            return Err(Error::InvalidNumConstraints);
        }

        let index_info = IndexInfo {
            num_copies,
            num_variables,
            num_constraints,
            max_weight,
            num_instance_variables: num_input_variables,
            f: PhantomData,
        };
        // println!("index_info: {:?}", index_info);
        let m = index_info.weight_nv();
        let n = index_info.constraints_nv();
        // println!("m: {}; n: {}", m, n);

        let a_arithmetization_time = start_timer!(|| "Arithmetizing A");
        let a_arith = arithmetize_matrix(&mut a, m, n);
        end_timer!(a_arithmetization_time);

        let b_arithmetization_time = start_timer!(|| "Arithmetizing B");
        let b_arith = arithmetize_matrix(&mut b, m, n);
        end_timer!(b_arithmetization_time);

        let c_arithmetization_time = start_timer!(|| "Arithmetizing C");
        let c_arith = arithmetize_matrix(&mut c, m, n);
        end_timer!(c_arithmetization_time);

        end_timer!(index_time);
        Ok(Index {
            index_info,

            a,
            b,
            c,

            a_arith,
            b_arith,
            c_arith,
        })
    }
}
