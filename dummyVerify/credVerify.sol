
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
        Pairing.G1Point[17] IC;
    }

    struct Proof {
        Pairing.G1Point A;
        Pairing.G2Point B;
        Pairing.G1Point C;
    }

    function verifyingKey() internal pure returns (VerifyingKey memory vk) {
        vk.alfa1 = Pairing.G1Point(uint256(3603385592142399165322038584737423078306046497913242803811228657239549949091), uint256(19121755434588687613374513413661890109184693036206707227117381283463167727096));
        vk.beta2 = Pairing.G2Point([uint256(12630293753508708938688430638978985288275802019023337016985702337271136341539), uint256(14494289187833486980337877743282916385889005433764941575324634346126833251596)], [uint256(2572690481778049583101287728036776498533089804825625532128443180125463550059), uint256(20254250104668976888515380855187964767907035679856297749453470948560762052691)]);
        vk.gamma2 = Pairing.G2Point([uint256(7991526463236724082685639523073133387629379433969540332303261763038912633039), uint256(7608571956075339803386116302409256313045561017572662962213255105045167706526)], [uint256(13515167448025810667146461120553535562181028035368383712729113193420000344044), uint256(14444297769351855817928398994543705352176789071620838839012266058488305335287)]);
        vk.delta2 = Pairing.G2Point([uint256(14508327609447894099905012343013686377026659642418360511383669536936206452860), uint256(11290082521138160495570813421205237796707636630668932070866371451499574208934)], [uint256(17053430449717489325908404280764214768118375416063146107215702693973303370891), uint256(2285551857440902567077849453855042986498897578936798920003178177170124972389)]);   
        vk.IC[0] = Pairing.G1Point(uint256(2608083429846578784934590953505983314082858535214662063096794728576731209532), uint256(3948357404432531491202027438766667794638284491298467897008930950500790312398));   
        vk.IC[1] = Pairing.G1Point(uint256(4007753535018631562181467488875544110881003932121521495686748098107836077008), uint256(5783190787605411150011325193962161761751713648949019279696940180201471754208));   
        vk.IC[2] = Pairing.G1Point(uint256(10566924504953351624075562731616756768632453715754514049769605759941133724569), uint256(4874562233062175398875288801911818216140057810078853884561920319916552432189));   
        vk.IC[3] = Pairing.G1Point(uint256(2328750183457425046521005556570947493515985472854237172243184057408080895610), uint256(14422593167906294013239806250115821725660473398487184947598834505124999616938));   
        vk.IC[4] = Pairing.G1Point(uint256(19121957339191112278138420575943810356032143226745947671266158737328937607239), uint256(9980034153696477375262863659091985179476023922873428566964134162183997281729));   
        vk.IC[5] = Pairing.G1Point(uint256(5748112254682906732364760131047339920649291878615985623225639784797291108241), uint256(18839455399388064822549152367669820545608880318617120462217653008713379034241));   
        vk.IC[6] = Pairing.G1Point(uint256(10278803407981421602561061030130739706481357130080636630781429592229464008200), uint256(21022798767272107874515534550220399687372330853960231124535880751737118176183));   
        vk.IC[7] = Pairing.G1Point(uint256(20284230176938719187935370310308912884817327563687577043198973832232733408370), uint256(17741699606669798836946270656172639009859253544609789623864524459805749233975));   
        vk.IC[8] = Pairing.G1Point(uint256(8491531546307030530472540374172161551882356712205146075812556961634752559355), uint256(13177742779118836187582272867244773572757998755310031900241857468009943927090));   
        vk.IC[9] = Pairing.G1Point(uint256(2307994903686959357689035236332394425876359764200486690273981662007169372249), uint256(2664586625932362038807334151482839090227685197315220610556359985010676841537));   
        vk.IC[10] = Pairing.G1Point(uint256(3538779197936062742589151123711331007459970177734585840821235122384157081621), uint256(15436903955432284535306511202299324104280755007281969032165921292844094516585));   
        vk.IC[11] = Pairing.G1Point(uint256(16817872400218620910693981767009098277618164280184588243486259289959296767482), uint256(9906442992654656349672762901630311123842570368468388940665567502814599123999));   
        vk.IC[12] = Pairing.G1Point(uint256(4043547426511741916537107260603954845347617172035099423297707894526465540393), uint256(3522431726148898936054904594467504470656974073361661833730210034213191829507));   
        vk.IC[13] = Pairing.G1Point(uint256(9404690914287413788455797027671818605186221763865994461723102422558038508743), uint256(5343609689846619127330020221732027653668650248538889398008466841656904739740));   
        vk.IC[14] = Pairing.G1Point(uint256(15886780061932357007459245802701206481486840287529361378913492529249971308581), uint256(18701187717669775893747293114924274398216887338612061610703628413995300977165));   
        vk.IC[15] = Pairing.G1Point(uint256(19336779001618305559616411872922712244386626716759973895851902812367751579231), uint256(16328249528288461027428607249796823546812376865214318293715389159544462763097));   
        vk.IC[16] = Pairing.G1Point(uint256(12211746840150345598759942170063128291023270087466754046869850806876737394779), uint256(20111749827458533544133208053135565715756199689705987876895397290502092471257));
    }
    
    /*
     * @returns Whether the proof is valid given the hardcoded verifying key
     *          above and the public inputs
     */
    function verifyProof(
        uint256[2] memory a,
        uint256[2][2] memory b,
        uint256[2] memory c,
        uint256[16] memory input
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
