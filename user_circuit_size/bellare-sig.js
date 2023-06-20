const chai = require("chai");
const path = require("path");
const wasm_tester = require("circom_tester").wasm;

const buildPoseidon = require("circomlibjs").buildPoseidon;

const assert = chai.assert;

describe("Poseidon Circuit test", function () {
    let poseidon;
    let F;

    this.timeout(1000000);

    before( async () => {
        poseidon = await buildPoseidon();
        F = poseidon.F;
        circuit = await wasm_tester(path.join(__dirname, "circuits", "poseidon_test.circom"));
        await circuit.loadConstraints();
        let num_constraints = circuit.constraints.length;
        console.log("Bellare SIG.Verify(pkU, pkW, sigmaW) := { Poseidon(pkU, pkW) = sigmaW }");
        console.log("Costs the same as Poseidon on 2 inputs");
        console.log("Poseidon (#inputs:", 2, ") #Constraints:", num_constraints);
    });

    it("Should check constraint of Poseidon([pkU, pkW])", async () => {
        // set dummy pkU and pkW values
        const w = await circuit.calculateWitness({inputs: [1, 2]});

        const res2 = poseidon([1,2]);

        assert(F.eq(F.e("7853200120776062878684798364095072458815029376092732009249414926327459813530"), F.e(res2)));
        await circuit.assertOut(w, {out : F.toObject(res2)});
        await circuit.checkConstraints(w);
    });
});
