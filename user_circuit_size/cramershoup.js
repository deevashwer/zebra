const chai = require("chai");
const path = require("path");

const wasm_tester = require("circom_tester").wasm;

const buildBabyJub = require("circomlibjs").buildBabyjub;
const buildPoseidon = require("circomlibjs").buildPoseidon;

const Scalar = require("ffjavascript").Scalar;
const assert = chai.assert;

const createBlakeHash = require("blake-hash");

async function buildCramerShoup() {
    const babyJub = await buildBabyJub("bn128");
    const poseidon = await buildPoseidon();
    return new CramerShoup(babyJub, poseidon);
}

class CramerShoup {

    constructor(babyJub, poseidon) {
        this.babyJub = babyJub;
        this.poseidon = poseidon;
        this.F = babyJub.F;
    }

    pruneBuffer(buff) {
        buff[0] = buff[0] & 0xF8;
        buff[31] = buff[31] & 0x7F;
        buff[31] = buff[31] | 0x40;
        return buff;
    }

    // deterministic setup
    setup() {
        const g1 = this.babyJub.Base8;
        const g2_exp_Buff = this.pruneBuffer(createBlakeHash("blake512").update('g2').update(Buffer.from("9999999999999999999999999999999999999999999999999999999999999999", "hex")).digest());
        let g2_exp = Scalar.fromRprLE(g2_exp_Buff, 0, 32);
        const g2 = this.babyJub.mulPointEscalar(g1, g2_exp);
        return {
            g1: g1,
            g2: g2,
        };
    }

    keyGen(prv) {
        const F = this.babyJub.F;
        const x1Buff = this.pruneBuffer(createBlakeHash("blake512").update('x1').update(Buffer.from(prv)).digest());
        const x2Buff = this.pruneBuffer(createBlakeHash("blake512").update('x2').update(Buffer.from(prv)).digest());
        const y1Buff = this.pruneBuffer(createBlakeHash("blake512").update('y1').update(Buffer.from(prv)).digest());
        const y2Buff = this.pruneBuffer(createBlakeHash("blake512").update('y2').update(Buffer.from(prv)).digest());
        const zBuff = this.pruneBuffer(createBlakeHash("blake512").update('z').update(Buffer.from(prv)).digest());
        let x1 = Scalar.fromRprLE(x1Buff, 0, 32);
        let x2 = Scalar.fromRprLE(x2Buff, 0, 32);
        let y1 = Scalar.fromRprLE(y1Buff, 0, 32);
        let y2 = Scalar.fromRprLE(y2Buff, 0, 32);
        let z = Scalar.fromRprLE(zBuff, 0, 32);
        let params = this.setup();
        let g1x1 = this.babyJub.mulPointEscalar(params.g1, x1);
        let g2x2 = this.babyJub.mulPointEscalar(params.g2, x2);
        let g1y1 = this.babyJub.mulPointEscalar(params.g1, y1);
        let g2y2 = this.babyJub.mulPointEscalar(params.g2, y2);
        let h = this.babyJub.mulPointEscalar(params.g1, z);
        let c = this.babyJub.addPoint(g1x1, g2x2);
        let d = this.babyJub.addPoint(g1y1, g2y2);

        return {
            Pk: {
                c: c,
                d: d,
                h: h,
            },
            Sk: {
                x1: x1,
                x2: x2,
                y1: y1,
                y2: y2,
                z: z,
            }
        };
    }

    encrypt(Pk, msg, rho) {
        let params = this.setup();

        let msgs = Scalar.e(this.babyJub.F.toObject(msg));
        let rhos = Scalar.e(this.babyJub.F.toObject(rho));
        let M = this.babyJub.mulPointEscalar(params.g1, msgs);
        let u1 = this.babyJub.mulPointEscalar(params.g1, rhos);
        let u2 = this.babyJub.mulPointEscalar(params.g2, rhos);
        let hrho = this.babyJub.mulPointEscalar(Pk.h, rhos);
        let e = this.babyJub.addPoint(hrho, M);

        let alpha = this.poseidon([u1[0], u1[1], u2[0], u2[1], e[0], e[1]]);
        let alphas = Scalar.e(this.babyJub.F.toObject(alpha));
        let drho = this.babyJub.mulPointEscalar(Pk.d, rhos);
        let drhoalpha = this.babyJub.mulPointEscalar(drho, alphas);
        let crho = this.babyJub.mulPointEscalar(Pk.c, rhos);
        let v = this.babyJub.addPoint(crho, drhoalpha);

        return {
            u1: u1,
            u2: u2,
            e: e,
            v: v,
        };
    }

    verifyDecrypt(Sk, C, msg) {
        let params = this.setup();
        let alpha = this.poseidon([C.u1[0], C.u1[1], C.u2[0], C.u2[1], C.e[0], C.e[1]]);
        let alphas = Scalar.e(this.babyJub.F.toObject(alpha));
        let msgs = Scalar.e(this.babyJub.F.toObject(msg));
        let M = this.babyJub.mulPointEscalar(params.g1, msgs);

        let u1z = this.babyJub.mulPointEscalar(C.u1, Sk.z);
        let e = this.babyJub.addPoint(u1z, M);
        if (!this.babyJub.F.eq(e[0], C.e[0])) return false;
        if (!this.babyJub.F.eq(e[1], C.e[1])) return false;

        let u1x1 = this.babyJub.mulPointEscalar(C.u1, Sk.x1);
        let u2x2 = this.babyJub.mulPointEscalar(C.u2, Sk.x2);
        let u1y1 = this.babyJub.mulPointEscalar(C.u1, Sk.y1);
        let u2y2 = this.babyJub.mulPointEscalar(C.u2, Sk.y2);
        let sumuiyi = this.babyJub.addPoint(u1y1, u2y2);
        let sumuixi = this.babyJub.addPoint(u1x1, u2x2);
        let alphasumuiyi = this.babyJub.mulPointEscalar(sumuiyi, alphas);
        let lhs = this.babyJub.addPoint(sumuixi, alphasumuiyi);
        if (!this.babyJub.F.eq(lhs[0], C.v[0])) return false;
        if (!this.babyJub.F.eq(lhs[1], C.v[1])) return false;

        return true;
    }
}

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


describe("CramerShoup test", function () {
    let circuit;
    let cramerShoup;
    let babyJub;
    let F;

    this.timeout(100000);

    before( async () => {
        cramerShoup = await buildCramerShoup();
        babyJub = await buildBabyJub();
        F = babyJub.F;
        circuit = await wasm_tester(path.join(__dirname, "circuits", "cramershoup.circom"));
        await circuit.loadConstraints();
        let num_constraints = circuit.constraints.length;
        console.log("CramerShoup #Constraints:", num_constraints);
    });


    it("Encrypt a message from BN254 Scalar Field", async () => {
        // dummy message and encryption randomness from BN254 Scalar Field
        const msg = F.e(1234);
        const rho = F.e(5678);

        const prvKey = Buffer.from("0001020304050607080900010203040506070809000102030405060708090001", "hex");

        const {Pk, Sk} = cramerShoup.keyGen(prvKey);

        const C = cramerShoup.encrypt(Pk, msg, rho);

        assert(cramerShoup.verifyDecrypt(Sk, C, msg));

        // let params = cramerShoup.setup();
        // console.log("g1[0]:", F.toObject(params.g1[0]));
        // console.log("g1[1]:", F.toObject(params.g1[1]));
        // console.log("g2[0]:", F.toObject(params.g2[0]));
        // console.log("g2[1]:", F.toObject(params.g2[1]));

        const input = {
            enabled: 1,
            Cx: F.toObject(Pk.c[0]),
            Cy: F.toObject(Pk.c[1]),
            Dx: F.toObject(Pk.d[0]),
            Dy: F.toObject(Pk.d[1]),
            Hx: F.toObject(Pk.h[0]),
            Hy: F.toObject(Pk.h[1]),
            U1x: F.toObject(C.u1[0]),
            U1y: F.toObject(C.u1[1]),
            U2x: F.toObject(C.u2[0]),
            U2y: F.toObject(C.u2[1]),
            Ex: F.toObject(C.e[0]),
            Ey: F.toObject(C.e[1]),
            Vx: F.toObject(C.v[0]),
            Vy: F.toObject(C.v[1]),
            msg: F.toObject(msg),
            rho: F.toObject(rho),
        };

        const w = await circuit.calculateWitness(input, true);

        await circuit.checkConstraints(w);

    });
});
