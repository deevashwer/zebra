package main

import (
	"crypto/rand"
	"math/big"
	"testing"

	"github.com/consensys/gnark-crypto/ecc/bn254"
	"github.com/consensys/gnark-crypto/ecc/bn254/fp"
)

type G1Affine = bn254.G1Affine
type G2Affine = bn254.G2Affine
type G1Jac = bn254.G1Jac
type G2Jac = bn254.G2Jac
type GT = bn254.GT

func genFp () fp.Element {
	var elmt fp.Element
	var b [fp.Bytes]byte
	rand.Read(b[:])
	elmt.SetBytes(b[:])
	return elmt
}

func genG1 () G1Jac {
	var g1Gen G1Jac
	g1Gen.X.SetString("1")
	g1Gen.Y.SetString("2")
	g1Gen.Z.SetString("1")
	return g1Gen
}

func genG1Affine () G1Affine {
	var g1Gen G1Affine
	g1GenJac := genG1()
	g1Gen.FromJacobian(&g1GenJac)
	return g1Gen
}

func genG2 () G2Jac {
	var g2Gen G2Jac
	g2Gen.X.SetString("10857046999023057135944570762232829481370756359578518086990519993285655852781",
		"11559732032986387107991004021392285783925812861821192530917403151452391805634")
	g2Gen.Y.SetString("8495653923123431417604973247489272438418190587263600148770280649306958101930",
		"4082367875863433681332203403145435568316851327593401208105741076214120093531")
	g2Gen.Z.SetString("1", "0")
	return g2Gen
}

func genG2Affine () G2Affine {
	var g2Gen G2Affine
	g2GenJac := genG2()
	g2Gen.FromJacobian(&g2GenJac)
	return g2Gen
}

func BenchmarkGTExp(b *testing.B) {
	var x GT
	var e fp.Element
	e.SetRandom()
	x.SetRandom()
	var _e big.Int
	k := new(big.Int).SetUint64(12)
	e.Exp(e, k)
	e.FromMont().ToBigInt(&_e)
	var a GT
	b.ResetTimer()
	for i := 0; i < b.N; i++ {
		a.Exp(&x, _e)
	}
}

func BenchmarkGTOp(b *testing.B) {
	var a, c GT
	a.SetRandom()
	c.SetRandom()
	b.ResetTimer()
	for i := 0; i < b.N; i++ {
		a.Mul(&a, &c)
	}
}

// Costs in Jacobian representation are lower
func BenchmarkG1Op(b *testing.B) {
	a := genG1()
	b.ResetTimer()
	for i := 0; i < b.N; i++ {
		a.AddAssign(&a)
	}
}

// func BenchmarkG1AffineOp(b *testing.B) {
// 	a := genG1Affine()
// 	b.ResetTimer()

// 	var res G1Affine
// 	for i := 0; i < b.N; i++ {
// 		res.Add(&a, &a)	
// 	}
// }

func BenchmarkG1Exp(b *testing.B) {
	a := genG1()
	var c big.Int
	genFp().ToBigIntRegular(&c)

	var res G1Jac
	b.ResetTimer()
	for i := 0; i < b.N; i++ {
		res.ScalarMultiplication(&a, &c)
	}
}

// func BenchmarkG1AffineExp(b *testing.B) {
// 	a := genG1Affine()
// 	var c big.Int
// 	genFp().ToBigIntRegular(&c)

// 	var res G1Affine
// 	b.ResetTimer()
// 	for i := 0; i < b.N; i++ {
// 		res.ScalarMultiplication(&a, &c)
// 	}
// }

func BenchmarkG2Op(b *testing.B) {
	a := genG2()
	b.ResetTimer()
	for i := 0; i < b.N; i++ {
		a.AddAssign(&a)
	}
}

// func BenchmarkG2AffineOp(b *testing.B) {
// 	a := genG2Affine()
// 	b.ResetTimer()

// 	var res G2Affine
// 	for i := 0; i < b.N; i++ {
// 		res.Add(&a, &a)	
// 	}
// }

func BenchmarkG2Exp(b *testing.B) {
	a := genG2()
	var c big.Int
	genFp().ToBigIntRegular(&c)

	var res G2Jac
	b.ResetTimer()
	for i := 0; i < b.N; i++ {
		res.ScalarMultiplication(&a, &c)
	}
}

// func BenchmarkG2AffineExp(b *testing.B) {
// 	a := genG2Affine()
// 	var c big.Int
// 	genFp().ToBigIntRegular(&c)

// 	var res G2Affine
// 	b.ResetTimer()
// 	for i := 0; i < b.N; i++ {
// 		res.ScalarMultiplication(&a, &c)
// 	}
// }

func BenchmarkPairing(b *testing.B) {
	a := genG1Affine()
	c := genG2Affine()

	b.ResetTimer()
	for i := 0; i < b.N; i++ {
		bn254.Pair([]G1Affine{a}, []G2Affine{c})
	}
}

// Groth16 has a pairing-product check of size 4, which is more efficient than doing 4 individual pairings.
func BenchmarkPairingProductCheck4(b *testing.B) {
	a := genG1Affine()
	c := genG2Affine()
	A := []G1Affine{a, a, a, a}
	C := []G2Affine{c, c, c, c}

	b.ResetTimer()
	for i := 0; i < b.N; i++ {
		bn254.Pair(A, C)
	}
}

// The cost of pairing product check is K_1 + n * K_2, where n is the number of products in the check, and K_1, K_2 are constants.
// In Groth16, we know that there's a single pairing-product check with n = 4
// The prior works don't report how many pairing-product checks they have; they simply report the number of pairings. Thus, to give them the benefit of doubt, we assume that they have a single pairing-product check.
// This benchmark is supposed to tell us the value of K_2, since K_1 should be amortized away when n = 1000.
func BenchmarkPairingProductCheck1000(b *testing.B) {
	a := genG1Affine()
	c := genG2Affine()
	A := make([]G1Affine, 1000)
	C := make([]G2Affine, 1000)
	for i := 0; i < 1000; i++ {
		A[i] = a
		C[i] = c
	}

	b.ResetTimer()
	for i := 0; i < b.N; i++ {
		bn254.Pair(A, C)
	}
}