pragma circom 2.0.0;

include "../../circomlib/circuits/poseidon.circom";
include "../../circomlib/circuits/bitify.circom";
include "../../circomlib/circuits/escalarmulany.circom";
include "../../circomlib/circuits/escalarmulfix.circom";

template CramerShoupEncryptVerifier() {
    signal input enabled;

    // public key
    signal input Cx;
    signal input Cy;
    signal input Dx;
    signal input Dy;
    signal input Hx;
    signal input Hy;

    // ciphertext
    signal input U1x;
    signal input U1y;
    signal input U2x;
    signal input U2y;
    signal input Ex;
    signal input Ey;
    signal input Vx;
    signal input Vy;

    // msg
    signal input msg;
    // encryption randomness
    signal input rho;

    var i;

    var G1[2] = [
        5299619240641551281634865583518297030282874472190772894086521144482721001553,
        16950150798460657717958625567821834550301663161624707787222815936182638968203
    ];

    var G2[2] = [
        20842787791685960819119847861024162269490459228146608927056917900006206582242,
        20208038431130868831841141693066500100831350985850946975923880902843168786546
    ];

// Calculate alpha = Poseidon(U1x, U1y, U2x, U2y, Ex, Ey)
    component hash = Poseidon(6);

    hash.inputs[0] <== U1x;
    hash.inputs[1] <== U1y;
    hash.inputs[2] <== U2x;
    hash.inputs[3] <== U2y;
    hash.inputs[4] <== Ex;
    hash.inputs[5] <== Ey;

    component alpha = Num2Bits_strict();
    alpha.in <== hash.out;

// calculate M = msg * g1
    component m = Num2Bits_strict();
    m.in <== msg;
    component M = EscalarMulFix(254, G1);
    for (i=0; i<254; i++) {
        M.e[i] <== m.out[i];
    }

// calculate rho_bits
    component rho_bits = Num2Bits_strict();
    rho_bits.in <== rho;
    
// calculate u1 = rho * g1
    component u1 = EscalarMulFix(254, G1);
    for (i=0; i<254; i++) {
        u1.e[i] <== rho_bits.out[i];
    }

// calculate u2 = rho * g2
    component u2 = EscalarMulFix(254, G2);
    for (i=0; i<254; i++) {
        u2.e[i] <== rho_bits.out[i];
    }

// calculate rho * h
    component hrho = EscalarMulAny(254);
    for (i=0; i<254; i++) {
        hrho.e[i] <== rho_bits.out[i];
    }
    hrho.p[0] <== Hx;
    hrho.p[1] <== Hy;

// calculate rho * d
    component drho = EscalarMulAny(254);
    for (i=0; i<254; i++) {
        drho.e[i] <== rho_bits.out[i];
    }
    drho.p[0] <== Dx;
    drho.p[1] <== Dy;

// calculate rho * c
    component crho = EscalarMulAny(254);
    for (i=0; i<254; i++) {
        crho.e[i] <== rho_bits.out[i];
    }
    crho.p[0] <== Cx;
    crho.p[1] <== Cy;

// calculate e = rho * h + M
    component e = BabyAdd();
    e.x1 <== M.out[0];
    e.y1 <== M.out[1];
    e.x2 <== hrho.out[0];
    e.y2 <== hrho.out[1];

// calculate alpha * drho
    component alphadrho = EscalarMulAny(254);
    for (i=0; i<254; i++) {
        alphadrho.e[i] <== alpha.out[i];
    }
    alphadrho.p[0] <== drho.out[0];
    alphadrho.p[1] <== drho.out[1];

// calculate v = crho + alphadrho
    component v = BabyAdd();
    v.x1 <== crho.out[0];
    v.y1 <== crho.out[1];
    v.x2 <== alphadrho.out[0];
    v.y2 <== alphadrho.out[1];

// u1 == U1
    component eqCheckU1x = ForceEqualIfEnabled();
    eqCheckU1x.enabled <== enabled;
    eqCheckU1x.in[0] <== u1.out[0];
    eqCheckU1x.in[1] <== U1x;
    component eqCheckU1y = ForceEqualIfEnabled();
    eqCheckU1y.enabled <== enabled;
    eqCheckU1y.in[0] <== u1.out[1];
    eqCheckU1y.in[1] <== U1y;

// u2 == U2
    component eqCheckU2x = ForceEqualIfEnabled();
    eqCheckU2x.enabled <== enabled;
    eqCheckU2x.in[0] <== u2.out[0];
    eqCheckU2x.in[1] <== U2x;
    component eqCheckU2y = ForceEqualIfEnabled();
    eqCheckU2y.enabled <== enabled;
    eqCheckU2y.in[0] <== u2.out[1];
    eqCheckU2y.in[1] <== U2y;

// e == E
    component eqCheckEx = ForceEqualIfEnabled();
    eqCheckEx.enabled <== enabled;
    eqCheckEx.in[0] <== e.xout;
    eqCheckEx.in[1] <== Ex;
    component eqCheckEy = ForceEqualIfEnabled();
    eqCheckEy.enabled <== enabled;
    eqCheckEy.in[0] <== e.yout;
    eqCheckEy.in[1] <== Ey;

// v == V
    component eqCheckVx = ForceEqualIfEnabled();
    eqCheckVx.enabled <== enabled;
    eqCheckVx.in[0] <== v.xout;
    eqCheckVx.in[1] <== Vx;
    component eqCheckVy = ForceEqualIfEnabled();
    eqCheckVy.enabled <== enabled;
    eqCheckVy.in[0] <== v.yout;
    eqCheckVy.in[1] <== Vy;
}

component main = CramerShoupEncryptVerifier();