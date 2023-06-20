
// SPDX-License-Identifier: AML
// 
// Copyright 2017 Christian Reitwiessner
// Permission is hereby granted, free of charge, to any person obtaining a copy
// of this software and associated documentation files (the "Software"), to
// deal in the Software without restriction, including without limitation the
// rights to use, copy, modify, merge, publish, distribute, sublicense, and/or
// sell copies of the Software, and to permit persons to whom the Software is
// furnished to do so, subject to the following conditions:
// The above copyright notice and this permission notice shall be included in
// all copies or substantial portions of the Software.
// THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
// IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
// FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
// AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
// LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
// FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS
// IN THE SOFTWARE.

// 2019 OKIMS

pragma solidity ^0.8.0;

library Pairing {

    uint256 constant PRIME_Q = 21888242871839275222246405745257275088696311157297823662689037894645226208583;

    struct G1Point {
        uint256 X;
        uint256 Y;
    }

    // Encoding of field elements is: X[0] * z + X[1]
    struct G2Point {
        uint256[2] X;
        uint256[2] Y;
    }

    /*
     * @return The negation of p, i.e. p.plus(p.negate()) should be zero. 
     */
    function negate(G1Point memory p) internal pure returns (G1Point memory) {

        // The prime q in the base field F_q for G1
        if (p.X == 0 && p.Y == 0) {
            return G1Point(0, 0);
        } else {
            return G1Point(p.X, PRIME_Q - (p.Y % PRIME_Q));
        }
    }

    /*
     * @return The sum of two points of G1
     */
    function plus(
        G1Point memory p1,
        G1Point memory p2
    ) internal view returns (G1Point memory r) {

        uint256[4] memory input;
        input[0] = p1.X;
        input[1] = p1.Y;
        input[2] = p2.X;
        input[3] = p2.Y;
        bool success;

        // solium-disable-next-line security/no-inline-assembly
        assembly {
            success := staticcall(sub(gas(), 2000), 6, input, 0xc0, r, 0x60)
            // Use "invalid" to make gas estimation work
            switch success case 0 { invalid() }
        }

        require(success,"pairing-add-failed");
    }

    /*
     * @return The product of a point on G1 and a scalar, i.e.
     *         p == p.scalar_mul(1) and p.plus(p) == p.scalar_mul(2) for all
     *         points p.
     */
    function scalar_mul(G1Point memory p, uint256 s) internal view returns (G1Point memory r) {

        uint256[3] memory input;
        input[0] = p.X;
        input[1] = p.Y;
        input[2] = s;
        bool success;
        // solium-disable-next-line security/no-inline-assembly
        assembly {
            success := staticcall(sub(gas(), 2000), 7, input, 0x80, r, 0x60)
            // Use "invalid" to make gas estimation work
            switch success case 0 { invalid() }
        }
        require (success,"pairing-mul-failed");
    }

    /* @return The result of computing the pairing check
     *         e(p1[0], p2[0]) *  .... * e(p1[n], p2[n]) == 1
     *         For example,
     *         pairing([P1(), P1().negate()], [P2(), P2()]) should return true.
     */
    function pairing(
        G1Point memory a1,
        G2Point memory a2,
        G1Point memory b1,
        G2Point memory b2,
        G1Point memory c1,
        G2Point memory c2,
        G1Point memory d1,
        G2Point memory d2
    ) internal view returns (bool) {

        G1Point[4] memory p1 = [a1, b1, c1, d1];
        G2Point[4] memory p2 = [a2, b2, c2, d2];
        uint256 inputSize = 24;
        uint256[] memory input = new uint256[](inputSize);

        for (uint256 i = 0; i < 4; i++) {
            uint256 j = i * 6;
            input[j + 0] = p1[i].X;
            input[j + 1] = p1[i].Y;
            input[j + 2] = p2[i].X[0];
            input[j + 3] = p2[i].X[1];
            input[j + 4] = p2[i].Y[0];
            input[j + 5] = p2[i].Y[1];
        }

        uint256[1] memory out;
        bool success;

        // solium-disable-next-line security/no-inline-assembly
        assembly {
            success := staticcall(sub(gas(), 2000), 8, add(input, 0x20), mul(inputSize, 0x20), out, 0x20)
            // Use "invalid" to make gas estimation work
            switch success case 0 { invalid() }
        }

        require(success,"pairing-opcode-failed");

        return out[0] != 0;
    }
}

contract Verifier {

    using Pairing for *;

    uint256 constant SNARK_SCALAR_FIELD = 21888242871839275222246405745257275088548364400416034343698204186575808495617;
    uint256 constant PRIME_Q = 21888242871839275222246405745257275088696311157297823662689037894645226208583;

    struct VerifyingKey {
        Pairing.G1Point alfa1;
        Pairing.G2Point beta2;
        Pairing.G2Point gamma2;
        Pairing.G2Point delta2;
        Pairing.G1Point[16] IC;
    }

    struct Proof {
        Pairing.G1Point A;
        Pairing.G2Point B;
        Pairing.G1Point C;
    }

    function verifyingKey() internal pure returns (VerifyingKey memory vk) {
        vk.alfa1 = Pairing.G1Point(uint256(12289719777427534885445137737804828548724061785823264124295371829754657603432), uint256(19652401379777296257141086065932761976026610661318486042902716035432220304100));
        vk.beta2 = Pairing.G2Point([uint256(9751813543126182346745753632230174200933375097273162182006919292816432420129), uint256(9336753156734523798943502878733368327857959309787353509506295837025360150649)], [uint256(17245312837852375158556774125828585103774714990481563536460545503208472857999), uint256(1534573117437337257958976370721282155313960118917624144407140692493578829957)]);
        vk.gamma2 = Pairing.G2Point([uint256(19400477357920207366164039550159379961131103753262268314852580425757460579570), uint256(10240765205145056926327917624240068377084818454836469021727740902639717543560)], [uint256(14462649955707332804497738210830039334795719980437750517093880167502564862233), uint256(15691063376415065701689688045008438753036156252197549212780766158422772285786)]);
        vk.delta2 = Pairing.G2Point([uint256(14018764862009802081641419044256285037275283787839021114876889706016848112511), uint256(12280754622395285812399587735036037310361285029694787694381481855460257091209)], [uint256(9669099350528365127703550385268512803930833806962346011678684717166601322831), uint256(15042356242917020336126286796936143747801205823463065991154087661287111865294)]);   
        vk.IC[0] = Pairing.G1Point(uint256(14635294644951643364067140568009032221348442779279255755961492648174857571830), uint256(8370535757538363388608490797705060206041451107789917784817478189655994391479));   
        vk.IC[1] = Pairing.G1Point(uint256(20956937344676804298328504704561466502925854415304607156703175713181614211913), uint256(6348997015607442813996923214098885359372454215803928726710510400583584901139));   
        vk.IC[2] = Pairing.G1Point(uint256(11626287701406536329878440534249914714301400399416147577747079443431240341888), uint256(11998804706581850034936898510038193564138184940277595396298682085886039813544));   
        vk.IC[3] = Pairing.G1Point(uint256(9917824612554595836710800070412777976327690715262754241480509681744082519677), uint256(9404851580711159242798081511416666805844333632229353060488011090092620079257));   
        vk.IC[4] = Pairing.G1Point(uint256(12233301284282386713414900198776537084771823986947985272457696604460565266658), uint256(1634446957144873785017990584567691134045566593706868051463598617450512807198));   
        vk.IC[5] = Pairing.G1Point(uint256(2863910721607460274830264788244721260749974557136007968486463873788573483848), uint256(1023215894577034245433146209649932081653514913516465138699846307750774710016));   
        vk.IC[6] = Pairing.G1Point(uint256(14254169426159148557862575411669995326782072570926078840877070859826655841251), uint256(13688280951713488644504473250990884106794227775385211245176585414367386499071));   
        vk.IC[7] = Pairing.G1Point(uint256(1128320900133372302715030555005982156125007877592220490782129138986853100346), uint256(15530434236925424161066404824261184866778738788948938987415852707633041973363));   
        vk.IC[8] = Pairing.G1Point(uint256(10863660635989823055929875170223195667112544282351713477122118895866843877173), uint256(11881395876910361229405323267929401884186434961180765474533966998168644358748));   
        vk.IC[9] = Pairing.G1Point(uint256(8695330563180075494799530451604248667068343056297892220130891629902564590542), uint256(9670227531927343662403581046292440044986818137351901989978914955082535119480));   
        vk.IC[10] = Pairing.G1Point(uint256(12687453499549948796742702189968323921985217232387974253987177305759903536077), uint256(3688556310254952128586214215125997544995513977514980849258614644074922642026));   
        vk.IC[11] = Pairing.G1Point(uint256(2513751089587314994751990699841387850775208860470662439337922894943945532460), uint256(16710451756764658458511592080024051316542934338168582058507886421810920731249));   
        vk.IC[12] = Pairing.G1Point(uint256(1851060808736423329877608029707016197910448648792581244928645794876379275997), uint256(945245218211366758138782593741089038068057797613551347281172155178366254914));   
        vk.IC[13] = Pairing.G1Point(uint256(10410795348015885066620788180057047174417421167986579211834196634005426331132), uint256(590349541532384070234131807156881745392134105429451194562329025541227681458));   
        vk.IC[14] = Pairing.G1Point(uint256(20978381489457016953136245800370861079669881306764508483089053321049019903181), uint256(4009997115573151284168593152547119401190371051260500455267167499850013677325));   
        vk.IC[15] = Pairing.G1Point(uint256(1934345801247308449670303178267669654670296163718481450818576217148363870216), uint256(5383717466358959041908615634287491056360862672574490545358243111880837953710));
    }
    
    /*
     * @returns Whether the proof is valid given the hardcoded verifying key
     *          above and the public inputs
     */
    function verifyProof(
        uint256[2] memory a,
        uint256[2][2] memory b,
        uint256[2] memory c,
        uint256[15] memory input
    ) public view returns (bool r) {

        Proof memory proof;
        proof.A = Pairing.G1Point(a[0], a[1]);
        proof.B = Pairing.G2Point([b[0][0], b[0][1]], [b[1][0], b[1][1]]);
        proof.C = Pairing.G1Point(c[0], c[1]);

        VerifyingKey memory vk = verifyingKey();

        // Compute the linear combination vk_x
        Pairing.G1Point memory vk_x = Pairing.G1Point(0, 0);

        // Make sure that proof.A, B, and C are each less than the prime q
        require(proof.A.X < PRIME_Q, "verifier-aX-gte-prime-q");
        require(proof.A.Y < PRIME_Q, "verifier-aY-gte-prime-q");

        require(proof.B.X[0] < PRIME_Q, "verifier-bX0-gte-prime-q");
        require(proof.B.Y[0] < PRIME_Q, "verifier-bY0-gte-prime-q");

        require(proof.B.X[1] < PRIME_Q, "verifier-bX1-gte-prime-q");
        require(proof.B.Y[1] < PRIME_Q, "verifier-bY1-gte-prime-q");

        require(proof.C.X < PRIME_Q, "verifier-cX-gte-prime-q");
        require(proof.C.Y < PRIME_Q, "verifier-cY-gte-prime-q");

        // Make sure that every input is less than the snark scalar field
        for (uint256 i = 0; i < input.length; i++) {
            require(input[i] < SNARK_SCALAR_FIELD,"verifier-gte-snark-scalar-field");
            vk_x = Pairing.plus(vk_x, Pairing.scalar_mul(vk.IC[i + 1], input[i]));
        }

        vk_x = Pairing.plus(vk_x, vk.IC[0]);

        return Pairing.pairing(
            Pairing.negate(proof.A),
            proof.B,
            vk.alfa1,
            vk.beta2,
            vk_x,
            vk.gamma2,
            proof.C,
            vk.delta2
        );
    }
}
