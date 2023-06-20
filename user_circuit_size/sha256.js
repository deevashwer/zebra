const chai = require("chai");
const path = require("path");
const crypto = require("crypto");
const F1Field = require("ffjavascript").F1Field;
const Scalar = require("ffjavascript").Scalar;
exports.p = Scalar.fromString("21888242871839275222246405745257275088548364400416034343698204186575808495617");
const Fr = new F1Field(exports.p);

const assert = chai.assert;

const sha256 = require("./helpers/sha256");

const wasm_tester = require("circom_tester").wasm;

// const printSignal = require("./helpers/printsignal");


function buffer2bitArray(b) {
    const res = [];
    for (let i=0; i<b.length; i++) {
        for (let j=0; j<8; j++) {
            res.push((b[i] >> (7-j) &1));
        }
    }
    return res;
}

function bitArray2buffer(a) {
    const len = Math.floor((a.length -1 )/8)+1;
    const b = new Buffer.alloc(len);

    for (let i=0; i<a.length; i++) {
        const p = Math.floor(i/8);
        b[p] = b[p] | (Number(a[i]) << ( 7 - (i%8)  ));
    }
    return b;
}


describe("SHA256 test", function () {
    this.timeout(100000);

    it("Should calculate a hash of 1 compressor", async () => {
        const cir = await wasm_tester(path.join(__dirname, "circuits", "sha256_512_test.circom"));
        await cir.loadConstraints();
        let num_constraints = cir.constraints.length;
        console.log("Tracing token tau = CR-PRF(tkU, eta) := { SHA256(tkU || eta) }, tkU size: 32 Bytes, eta size: 32 Bytes");
        console.log("Tracing key commitment zeta = Comm(tkU, omega) := { SHA256(tkU || omega) }, tkU size: 32 Bytes, omega size: 32 Bytes");
        console.log("Both cost the same as SHA256 on 64 Bytes");
        console.log("SHA256 (64 Bytes) #Constraints:", num_constraints);

        const b = new Buffer.alloc(64);
        for (let i=0; i<64; i++) {
            b[i] = i+1;
        }

        const hash = crypto.createHash("sha256")
            .update(b)
            .digest("hex");

        const arrIn = buffer2bitArray(b);
        const witness = await cir.calculateWitness({ "in": arrIn }, true);

        const arrOut = witness.slice(1, 257);
        const hash2 = bitArray2buffer(arrOut).toString("hex");

        assert.equal(hash, hash2);
    }).timeout(1000000);

    it("Should calculate a hash of 2 compressor", async () => {
        const cir = await wasm_tester(path.join(__dirname, "circuits", "sha256_2560_test.circom"));
        await cir.loadConstraints();
        let num_constraints = cir.constraints.length;
        console.log("Token commitment nu = CRH(alpha, gamma) = { SHA256(alpha || gamma) }, alpha size: 256 Bytes, gamma size: 64 Bytes");
        console.log("Costs the same as SHA256 on 320 Bytes");
        console.log("SHA256 (320 Bytes) #Constraints:", num_constraints);

        const b = new Buffer.alloc(320);
        for (let i=0; i<320; i++) {
            b[i] = i+1;
        }

        const hash = crypto.createHash("sha256")
            .update(b)
            .digest("hex");

        const arrIn = buffer2bitArray(b);
        const witness = await cir.calculateWitness({ "in": arrIn }, true);

        const arrOut = witness.slice(1, 257);
        const hash2 = bitArray2buffer(arrOut).toString("hex");

        assert.equal(hash, hash2);

    }).timeout(1000000);

});
