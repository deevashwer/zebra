# ZEBRA: SNARK-based Anonymous Credentials for Practical, Private and Accountable On-chain Access Control

This repository hosts the code to benchmark ZEBRA. 

## Dependencies
- `go v1.20.4`
- `node v20.0.0` (`npm v9.6.4`)
- `cargo v1.64.0`
- `circom v2.1.4`

You can install all dependences by running the script `install_dependencies.sh`. After running this script, make sure to run the following command `source ~/.bashrc` to bring all dependencies into the scope of the PATH variable.

# Benchmarks

## Smart Contracts
First, spin up a local Ethereum blockchain using Ganache by running `npm run ganache_start` in a separate terminal. Now, you can benchmark the gas costs for the ZEBRA smart contracts as follows:
* **Credential Verification**: `npm run cred_verify_test`
* **Batched L1 Verification**: `npm run batch_L1_test`
* **Batched L2 Verification**: `npm run batch_L2_test`

To benchmark these contracts, we create dummy transactions with dummy Groth16 SNARK proofs. Groth16 proofs have constant verification complexity which is independent of the circuit and only depends on the number of public inputs. Thus, we can accurately benchmark the gas costs for ZEBRA smart contracts by creating dummy proofs with varying number of public inputs.
**The dummy transactions and proofs have already been generated and included as part of this repository**. In case you want to generate the dummy proofs yourself, you can follow the instructions below.

The dummy proofs are generated using the `dummyContractCircuits.sh` script. This script takes the contract name as an argument and generates the corresponding dummy proof. For example, to generate a dummy proof for the `CredentialVerification` contract, run `./dummyContractCircuits.sh CredVerify`, which will generate the following files:
* `dummyVerify/CredVerify.sol`: a Solidity contract that implements the logic for verifying the dummy `CredVerify` proof. This logic then needs to copied to our `contract/contracts/zebra-core.sol` contract.
* `contract/test/data/{CredVerify_proof.json,CredVerify_witness.json}`: the dummy proof and witness data, respectively. These files are used by the test file `contract/test/cred-verify-test.js` to benchmark the corresponding `zebra-core.sol` contract.

Similarly, you can generate dummy proofs for `{BatchL1-64, BatchL2-64, BatchL1-512, BatchL2-512}`.

## Credential Verification Circuit Size and User Overhead
First clone the `circomlib` submodule by running `git submodule update --init`. Then run `npm run user_circuit_size` in the top-level directory. This will output the number of constraints for each subcomponent of the credential verification circuit. Sum these numbers to get the total number of constraints for the credential verification circuit.

The user computation primarily consists of generating a Groth16 proof for the credential verification circuit. To benchmark the user overhead, we run a dummy circuit with the same number of constraints as the credential verification circuit. You can use the `bench_groth16.sh` script to benchmark circuits with arbitrary number of constraints. For ease of use, we've hardcoded the number of constraints for the credential verification circuit in the script, so that you can simply benchmark the user overhead by running `bash -x bench_groth16.sh CredVerify`.

## Aggregator Overhead
The aggregator computation consists of generating a Spartan proof that verifies all user proofs, followed by generating a Groth16 proof that verifies the Spartan proof. To benchmark the aggregator overhead, we benchmark both steps separately.

#### Spartan Proof Generation
Follow the instructions below to benchmark Spartan proof generation cost for 64 and 512 users. The benchmark will output the Spartan proof generation time as well as the total number of constraints required to verify this Spartan proof.
```
cd simd-spartan
cargo build --release
// 64 users
cargo test --release zebra::tests::test_med -- --nocapture
// 512 users
cargo test --release zebra::tests::test_big -- --nocapture
```

#### Groth16 Proof Generation
Given the number of constraints for verifying a Spartan proof from the step above, we can use the `bench_groth16.sh` script to benchmark the Groth16 proof generation cost. We've also hardcoded the number of constraints to verify the Spartan proof for 64 and 512 users in this script, so that you can simply benchmark the Groth16 proof generation cost by running `bash -x bench_groth16.sh {Aggregator64/Aggregator512}`.

## BN254 Curve Operations
We estimate verifier time of prior anonymous credential (AC) schemes by benchmarking elliptic curve operations on the BN254 curves. For this experiment, we consider the same curve implementation as `gnark`, i.e., the Groth16 library we use.
You can run these benchmarks on your system by running: `bash -x bench_bn254.sh`. This script will benchmark the following operations: `op-G1, exp-G1, op-G2, exp-G2, op-GT, exp-GT, Pairing`.

**Note**: Typically, AC schemes use pairing product checks instead of computing each pairing operation independently. The cost of pairing product check is `K_1 + n * K_2`, where `n` is the number of products in the check, `K_1, K_2` are constants, and `K_2` is smaller than the cost of computing an individual pairing. The prior works don't report how many pairing-product checks they have; they simply report the number of pairings. To give them the benefit of doubt, we assume that they have a single pairing-product check with all the pairings. We estimate `K_1` and `K_2` by benchmarking a pairing product check with `n=1` and `n=1000`.