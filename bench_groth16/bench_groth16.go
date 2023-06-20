// Copyright 2020 ConsenSys AG
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

package main

import (
	"fmt"
	"strconv"
	"time"

	"github.com/consensys/gnark-crypto/ecc"
	"github.com/consensys/gnark/backend"
	"github.com/consensys/gnark/backend/groth16"
	"github.com/consensys/gnark/frontend"
	"github.com/consensys/gnark/std/hash/mimc"
)

var r1csConstraintsString string
var r1csConstraints, _ = strconv.Atoi(r1csConstraintsString)
const mimcConstraints = 273
var reps = (r1csConstraints + mimcConstraints - 1)/mimcConstraints

// Circuit defines a pre-image knowledge proof
// mimc(secret preImage) = public hash
type Circuit struct {
	PreImage []frontend.Variable
	Hash     []frontend.Variable `gnark:",public"`
}

// Define declares the circuit's constraints
// Hash = mimc(PreImage)
func (circuit *Circuit) Define(api frontend.API) error {
	// hash function
	for i := 0; i < reps; i++ {
		mimc, _ := mimc.NewMiMC(api)

		// specify constraints
		// mimc(preImage) == hash
		mimc.Write(circuit.PreImage[i])
		result := mimc.Sum()
		api.AssertIsEqual(circuit.Hash[i], result)
	}
	return nil
}

func main() {
	// runtime.GOMAXPROCS(1)

	circuit := Circuit {
		PreImage: make([]frontend.Variable, reps),
		Hash: make([]frontend.Variable, reps),
	}
	start := time.Now()
	r1cs, err := frontend.Compile(ecc.BN254, backend.GROTH16, &circuit)
	t := time.Now()
	elapsed := t.Sub(start)
	fmt.Printf("Compile elapsed: %v\n", elapsed)
	if err != nil {
		fmt.Printf("err: %v\n", err)
	}
	var internal, secret, public = r1cs.GetNbVariables()
	fmt.Printf("r1cs.GetNbConstraints(): %v\n", r1cs.GetNbConstraints())
	fmt.Printf("public, secret, internal %v, %v, %v\n", public, secret, internal)
	if err != nil {
		fmt.Printf("err: %v\n", err)
	}
	// generating pk, vk
	start = time.Now()
	pk, vk, err := groth16.Setup(r1cs)
	t = time.Now()
	elapsed = t.Sub(start)
	fmt.Printf("Setup elapsed: %v\n", elapsed)

	PreImage := make([]frontend.Variable, reps)
	Hash := make([]frontend.Variable, reps)
	for i := 0; i < reps; i++ {
		PreImage[i] = "16130099170765464552823636852555369511329944820189892919423002775646948828469"
		Hash[i] = "8674594860895598770446879254410848023850744751986836044725552747672873438975"
	}
	assignment := Circuit {
		PreImage: PreImage,
		Hash: Hash,
	}

	witness, err := frontend.NewWitness(&assignment, ecc.BN254)
	publicWitness, err := frontend.NewWitness(&assignment, ecc.BN254, frontend.PublicOnly())
	start = time.Now()
	// generate the proof
	proof, err := groth16.Prove(r1cs, pk, witness)
	t = time.Now()
	elapsed = t.Sub(start)
	fmt.Printf("proving elapsed: %v\n", elapsed)
	start = time.Now()
	err = groth16.Verify(proof, vk, publicWitness)
	t = time.Now()
	elapsed = t.Sub(start)
	fmt.Printf("verify elapsed: %v\n", elapsed)
}
