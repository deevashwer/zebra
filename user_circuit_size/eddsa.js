const chai = require("chai");
const path = require("path");

const wasm_tester = require("circom_tester").wasm;

const buildEddsa = require("circomlibjs").buildEddsa;
const buildBabyjub = require("circomlibjs").buildBabyjub;

const Scalar = require("ffjavascript").Scalar;

const assert = chai.assert;

function print(circuit, w, s) {
    console.log(s + ": " + w[circuit.getSignalIdx(s)]);
}

function buffer2bits(buff) {
    const res = [];
    for (let i=0; i<buff.length; i++) {
        for (let j=0; j<8; j++) {
            if ((buff[i]>>j)&1) {
                res.push(1n);
            } else {
                res.push(0n);
            }
        }
    }
    return res;
}


describe("EdDSA test", function () {
    let circuit;
    let eddsa;
    let babyJub;
    let F;

    this.timeout(100000);

    before( async () => {
        eddsa = await buildEddsa();
        babyJub = await buildBabyjub();
        F = babyJub.F;
        circuit = await wasm_tester(path.join(__dirname, "circuits", "eddsa_test.circom"));
        await circuit.loadConstraints();
        let num_constraints = circuit.constraints.length;
        let msg_length = 96
        console.log("EdDSA (Pedersen, msg_length:", msg_length, "Bytes) #Constraints:", num_constraints);
        console.log("pkU size with Bellare Signature: 32 Bytes, zeta size with SHA256: 32 Bytes, assuming attr size: 32 Bytes");
    });


    it("Sign a message of 64 Bytes", async () => {
        // dummy message of 64 Bytes
        const msg = Buffer.from("000102030405060708091011121314151617181920212223242526272829303100010203040506070809101112131415161718192021222324252627282930310001020304050607080910111213141516171819202122232425262728293031", "hex");

        const prvKey = Buffer.from("0001020304050607080900010203040506070809000102030405060708090001", "hex");

        const pubKey = eddsa.prv2pub(prvKey);

        const pPubKey = babyJub.packPoint(pubKey);

        const signature = eddsa.signPedersen(prvKey, msg);

        const pSignature = eddsa.packSignature(signature);
        const uSignature = eddsa.unpackSignature(pSignature);

        assert(eddsa.verifyPedersen(msg, uSignature, pubKey));

        const msgBits = buffer2bits( msg);
        const r8Bits = buffer2bits( pSignature.slice(0, 32));
        const sBits = buffer2bits( pSignature.slice(32, 64));
        const aBits = buffer2bits( pPubKey);

        const w = await circuit.calculateWitness({A: aBits, R8: r8Bits, S: sBits, msg: msgBits}, true);

        await circuit.checkConstraints(w);
    });
});
