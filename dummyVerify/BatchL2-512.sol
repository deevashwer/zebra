
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
        Pairing.G1Point[18] IC;
    }

    struct Proof {
        Pairing.G1Point A;
        Pairing.G2Point B;
        Pairing.G1Point C;
    }

    function verifyingKey() internal pure returns (VerifyingKey memory vk) {
        vk.alfa1 = Pairing.G1Point(uint256(7400906440673956495885894732702131022494541513638107746289057513792837952675), uint256(5972787944824720034331550419278311647980858772845581475829597107941698330897));
        vk.beta2 = Pairing.G2Point([uint256(11215854432395513710223826383905088785547518293805973350633554789406151492330), uint256(3716530940089781235194425253857565674330012339144244235998016087896337652718)], [uint256(10260027811047374025826442770565934455903241263950946049658329631681291552695), uint256(6115379076203879340310057202776790323883729068249518128196531930273785215131)]);
        vk.gamma2 = Pairing.G2Point([uint256(17609949070736680609549428665001085292172468103308703662551745477198649584237), uint256(9301311913903719747790560828976260331258739865834940988285797804131456452249)], [uint256(7613841789035759840768109128695745474658816086570063442610862136991010388829), uint256(136605177189251699195483140750400369622409340724328551947695718851397557107)]);
        vk.delta2 = Pairing.G2Point([uint256(20392288826651299129345420521826743012310705949418655063895162014759638560667), uint256(1929326733857192990285604178242046653214499760074747547061473425731519851605)], [uint256(7004878665613499502792992333442190258119460889074515161672181616937880158422), uint256(19625479894966322627668253967504393912399368209346328857455540009594454904299)]);   
        vk.IC[0] = Pairing.G1Point(uint256(5543766432070518045422131816057624009356692246466221428370920544117333709961), uint256(13628991822138585500937689807509855898930239608519025405305578166368656806899));   
        vk.IC[1] = Pairing.G1Point(uint256(2372715977816482462928371443873787851611984828276285523351784980078162880594), uint256(8165933322139568761831418271585878476486697651930650692423858323445686488937));   
        vk.IC[2] = Pairing.G1Point(uint256(19420463572449367072892943272265270089979707845591168533869419668593455148101), uint256(19180969674093102779830300725402443394223413435337729100139408486864337309332));   
        vk.IC[3] = Pairing.G1Point(uint256(9026677624380422956552576264874402043519089303471819219681734931686421098678), uint256(20354171724050421293223486874684166314173118385820375286991515431613341977422));   
        vk.IC[4] = Pairing.G1Point(uint256(9068335232399863829769712172230149378184220320943660436458996179625714074042), uint256(8141771802658676765392917307136815480140665103130986216719251007810306222868));   
        vk.IC[5] = Pairing.G1Point(uint256(2813747775031786814441555188133374347847435581128410819207758334326423396945), uint256(16046509623681873225556070353003357902489898072156907647150561491824804015027));   
        vk.IC[6] = Pairing.G1Point(uint256(1880552836611278014844939219890199617986091983338079685963815397640588864072), uint256(21244056802096935141262363918519224304640210042605745715645058530329232596755));   
        vk.IC[7] = Pairing.G1Point(uint256(20915782475220260404111874335936621312893526603877554226305586496886638116421), uint256(7725214554513394752684154028190744888281594440223853613688506754430950421136));   
        vk.IC[8] = Pairing.G1Point(uint256(18243989103356883074557348120705514229672024854740459763096978102435586166776), uint256(5690044797696443569046948513269273607559892462130914807634930453206425680222));   
        vk.IC[9] = Pairing.G1Point(uint256(1772472455888711891328853258548620269767520286353734084509620764619611203713), uint256(16009876268116096005477048831877646289202142185851334915710669297350313685195));   
        vk.IC[10] = Pairing.G1Point(uint256(17115115895892234899297160863837114728536251535382842651705768159679450584725), uint256(13579267055325682007176703470772333495545895839664846067043343834546860339036));   
        vk.IC[11] = Pairing.G1Point(uint256(3207809327593070220107441463595577402404562792282398602061146494158103212330), uint256(406461247884280089280425188688782329028181028574868769692566295503900760964));   
        vk.IC[12] = Pairing.G1Point(uint256(16863686828705427949077910404459181319432223447292757926707070238063904399967), uint256(1523972695205404583787081737452472032628223026688638694735533455038690505738));   
        vk.IC[13] = Pairing.G1Point(uint256(18476949102511059517201984700060352335744588784580509717843740543118763802637), uint256(17668475352726704864280370367832248674808424728243579369457011324157794816048));   
        vk.IC[14] = Pairing.G1Point(uint256(18713804727451410367109748281586298533020071795815624836063339359338805849795), uint256(12988786458805922255377618070789937605821681571243018498164313424336078544549));   
        vk.IC[15] = Pairing.G1Point(uint256(17240798926856360724258236101902840844994900554808222798788961163331916720084), uint256(10394496726558316736981468808291281871880265856387669958850064830482559697717));   
        vk.IC[16] = Pairing.G1Point(uint256(12912460238126398593699745102972207508368467851772002585005354513781697878866), uint256(20728345302375313703603076161857751032607776112220016576070949908943894416455));   
        vk.IC[17] = Pairing.G1Point(uint256(12434254065095519160181459413916344269789694568554508093975728974688407588304), uint256(20237834513386030114820129087162438164138390648859272713110907330812586021087));
    }
    
    /*
     * @returns Whether the proof is valid given the hardcoded verifying key
     *          above and the public inputs
     */
    function verifyProof(
        uint256[2] memory a,
        uint256[2][2] memory b,
        uint256[2] memory c,
        uint256[17] memory input
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
