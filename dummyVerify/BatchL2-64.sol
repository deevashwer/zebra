
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
        vk.alfa1 = Pairing.G1Point(uint256(9447355015739809789109658678579137746545470540647779320435768490411539040537), uint256(7697371205813528422898799245827455065713886026121174530099206856388457401466));
        vk.beta2 = Pairing.G2Point([uint256(16654878645347337231899769121671423532300035346518871590709980720528299056758), uint256(13895314935036653963896030509441008631947504200065513142870222681025250049705)], [uint256(17227358527800545380224119077823697635597722142659474073561336478918883590544), uint256(14401595103134200176061255378134093651089486621730415497314453942489405688408)]);
        vk.gamma2 = Pairing.G2Point([uint256(20031091722256464197931342068071953375595746046223890461929203157018032089153), uint256(2933597674803091497128476802465311530708423120494467043600511173275300623795)], [uint256(9801331879725076147137008959433233871513360574198884059990218145734142032657), uint256(18622462855393799596661269260958276744637918467376437278073146486013613401487)]);
        vk.delta2 = Pairing.G2Point([uint256(7055649422894075291654440014633164995592347236986466928408932581780777819658), uint256(13842906733095198024847344228643686108055833927556424543179612996075870210929)], [uint256(20013837852256607416824593326895306721839232015033447687078122949534843621777), uint256(17223178980440589953890414658401730491751543512667235930293979168382460338144)]);   
        vk.IC[0] = Pairing.G1Point(uint256(14294547552781058269484999117922611675094124477176623089116103379872837889767), uint256(12552227529693301863242735852475035937273466979770012252066376016511475421554));   
        vk.IC[1] = Pairing.G1Point(uint256(2969176544272840627575774958377941926935828823987895700340515131938696552763), uint256(7819165925936706831782193955343877020790751544727408816414464805269708972470));   
        vk.IC[2] = Pairing.G1Point(uint256(10888758629776334614316270302721557291465793216656753110959160484749604676653), uint256(10128019220655326551002092071468553400189834842746115272547226946877643967661));   
        vk.IC[3] = Pairing.G1Point(uint256(9921957204663621623446029393560013533949150824486954484642645598566742961848), uint256(13929566877773355130810392073705080672755011548455709548030055662997393629435));   
        vk.IC[4] = Pairing.G1Point(uint256(15993922219866608329621402561764024627525367996207506299124207312555315523233), uint256(13363634503388397442621145003196361514150691042398858208887514662928343602247));   
        vk.IC[5] = Pairing.G1Point(uint256(10000586026411727273201491364805882873555276655293427853412381525752308800386), uint256(14795919579450813582900863287588759148660074804121957412766699167919478503760));   
        vk.IC[6] = Pairing.G1Point(uint256(18947678433500337064139710547558108335894534616762383183726600511078998563828), uint256(11548923891416601537352022283344176548924766291907240107253520800047839374554));   
        vk.IC[7] = Pairing.G1Point(uint256(18118637936294989110465288363022060950994532039969218663549924048100316824582), uint256(7737165857235449347478860300010313052948988148230717174861459624537413865430));   
        vk.IC[8] = Pairing.G1Point(uint256(19655288968440177049884861894156192968951181115333358607421310074069325173727), uint256(12440445053657235386263565117400977063633435292484061059914988576808117542869));   
        vk.IC[9] = Pairing.G1Point(uint256(3565684815385189201135204847900104183290544013768121308651661824645537851394), uint256(17975033443649621577489590589479270732464668899940776908544511762606037395878));   
        vk.IC[10] = Pairing.G1Point(uint256(7126616069889248715361217464408751293875831154730760110890996669153804132121), uint256(14103617706855694429024193808812906814619629230292911260618601908549733353192));   
        vk.IC[11] = Pairing.G1Point(uint256(4937163090525729168445090498125324158675528524468634944926246898238151400085), uint256(8557592072524017537077623211975450445369005036242641592643722660267449607555));   
        vk.IC[12] = Pairing.G1Point(uint256(16357539805083395789750004795438347795299315900821806713923080726913560434031), uint256(11936326946452741024629032306161485184691122348254520872104364242988154381571));   
        vk.IC[13] = Pairing.G1Point(uint256(9457183585751350019818476929694823073904526696690361814695354847666112921554), uint256(5020963181717053268789191117677264155925456097376684638762776898370736765526));   
        vk.IC[14] = Pairing.G1Point(uint256(9479268756208810870774659426698126361110174413594452174087542719880789672902), uint256(4242752850948526481527574264517363395463896615100328476038059534322535592073));   
        vk.IC[15] = Pairing.G1Point(uint256(6331677673201412017554361270438646052295454748091021158319878500564218257932), uint256(15054774816592219810345908367994252909454566769935592772232482696068185633385));   
        vk.IC[16] = Pairing.G1Point(uint256(20344738525015310537146521300640157959013755595463866907535210449598323277037), uint256(15784097601532233836897096785431386037932865990691291865324555605453553894287));   
        vk.IC[17] = Pairing.G1Point(uint256(18342225167803583999828602394248354505989585973645973450222005969436854512618), uint256(3970828288712598983248947137342200088648568502880172419259807406499799415712));
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
