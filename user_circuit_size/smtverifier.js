const chai = require("chai");
const path = require("path");
const Scalar = require("ffjavascript").Scalar;
const wasm_tester = require("circom_tester").wasm;

const newMemEmptyTrie = require("circomlibjs").newMemEmptyTrie;

const assert = chai.assert;

function print(circuit, w, s) {
    console.log(s + ": " + w[circuit.getSignalIdx(s)]);
}

let tree_depth = 254;

async function testExclusion(tree, _key, circuit) {
    const key = tree.F.e(_key);
    const res = await tree.find(key);

    assert(!res.found);
    let siblings = res.siblings;
    for (let i=0; i<siblings.length; i++) siblings[i] = tree.F.toObject(siblings[i]);
    while (siblings.length<tree_depth) siblings.push(0);

    const w = await circuit.calculateWitness({
        enabled: 1,
        fnc: 1,
        root: tree.F.toObject(tree.root),
        siblings: siblings,
        oldKey: res.isOld0 ? 0 : tree.F.toObject(res.notFoundKey),
        oldValue: res.isOld0 ? 0 : tree.F.toObject(res.notFoundValue),
        isOld0: res.isOld0 ? 1 : 0,
        key: tree.F.toObject(key),
        value: 0
    });

    await circuit.checkConstraints(w);

}

describe("SMT Verifier test", function () {
    let Fr;
    let circuit;
    let tree;

    this.timeout(100000);

    before( async () => {
        circuit = await wasm_tester(path.join(__dirname, "circuits", "smtverifier_test.circom"));
        await circuit.loadConstraints();
        let num_constraints = circuit.constraints.length;
        console.log("SMTVerifier Non-Membership Proof (Poseidon, tree_depth:", tree_depth, ") #Constraints:", num_constraints);
        console.log("#pkU bits: 254");

        tree = await newMemEmptyTrie();
        Fr = tree.F;
        await tree.insert(7,77);
        await tree.insert(8,88);
        await tree.insert(32,3232);
    });

    it("Check exclusion in a tree of 3", async () => {
        await testExclusion(tree, 0, circuit);
        await testExclusion(tree, 6, circuit);
        await testExclusion(tree, 9, circuit);
        await testExclusion(tree, 33, circuit);
        await testExclusion(tree, 31, circuit);
        await testExclusion(tree, 16, circuit);
        await testExclusion(tree, 64, circuit);
    });

});
