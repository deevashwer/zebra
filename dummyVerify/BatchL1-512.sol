
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
        vk.alfa1 = Pairing.G1Point(uint256(6563977883732811330675543194825946698941021026678696527778562236269113896959), uint256(4937106153752684445547414324007427040396510694266023423419077555436488926107));
        vk.beta2 = Pairing.G2Point([uint256(17547496889461930570515888092197669448999907659397872202226972085579088666768), uint256(4798432952190449007692301319783162692682524028593351943333038391781401002237)], [uint256(19472833188917775157865387705288622031193271412655361069544634866478850496475), uint256(2762377570638359188777087027540419868532912380405070289615094547520789455879)]);
        vk.gamma2 = Pairing.G2Point([uint256(18538545850608172238316610966751249652866141086165690797510864348403570172709), uint256(4192229961535006251620313798573425080139886364030986502485282969261432573128)], [uint256(309011391149750478009227244373345970418308095374227046971919742934134288039), uint256(16758627947761878054381781695689503212001430526484981778251234481132962792461)]);
        vk.delta2 = Pairing.G2Point([uint256(15584113302722317414525970682802637451065581297554315361490175083784022487796), uint256(2860579515286886940183459512166367500233376585618360449754782646614821245608)], [uint256(8956022083685569461735129803116013095738114340585119100288676275454119402906), uint256(14445898497342470928572588201265540800606834510835029781874451355034421521372)]);   
        vk.IC[0] = Pairing.G1Point(uint256(5265579154874342258042227943355500085271256821371125463642120496290181008492), uint256(19732498967479857091220197603594364704179455680163597421169401017499742259911));   
        vk.IC[1] = Pairing.G1Point(uint256(9655213482385104007796050365771443698801872929490042657859194206608632080625), uint256(591041876788294830107697121206840836802820293700704640873306650147033396010));   
        vk.IC[2] = Pairing.G1Point(uint256(18847042292236469891259088877483659860466841906187975880550031603907254089500), uint256(19339730071337786451605901475621505866416187998388651815153766251087008157843));   
        vk.IC[3] = Pairing.G1Point(uint256(8070552797987829392993779626083724135074684053271611759397502689248267680794), uint256(20567364894912981693442921914414011102157741331169228208052556267294621450065));   
        vk.IC[4] = Pairing.G1Point(uint256(9900667814891210725525400281470866485639809055575924400532408937536519866383), uint256(21112342083082572288612223863940447415148442903283537167666564344346024522244));   
        vk.IC[5] = Pairing.G1Point(uint256(11728877608834044854541710530878603799383098374184293355999396150095404868998), uint256(5637061131050718739445928727403259391487360331365659759975197154883056451392));   
        vk.IC[6] = Pairing.G1Point(uint256(21363626563173040915680692770931815571988730842455197113140109900178311765196), uint256(6841173744076221263380576638859984336857701974955833385837274153093066326449));   
        vk.IC[7] = Pairing.G1Point(uint256(15250840587493309841012587125716412606834469636435243004811531430468752617957), uint256(11630883497577041187981337671539866713087141061754260808005994632493976835935));   
        vk.IC[8] = Pairing.G1Point(uint256(6122860036286046371131616909298878793626315120878926850932836769057908602784), uint256(3603658273191055367066192376446114877432207701426513802298489026508644376939));   
        vk.IC[9] = Pairing.G1Point(uint256(15413229535883624200531296403457804854314996187758930474610786805472453598442), uint256(11106256631957628895855784324203928703180097984556056191622193389398096579491));   
        vk.IC[10] = Pairing.G1Point(uint256(9682325478336995680919782180646125575166573706232385469536552624632086155141), uint256(20839743793584161009666956692007643920803600006134189557643448102966335926352));   
        vk.IC[11] = Pairing.G1Point(uint256(10797287815820028564854422018116804095404865434531618100738187090063773457221), uint256(1092077292848281596403424523988284281430740899095313908872086247458618002843));   
        vk.IC[12] = Pairing.G1Point(uint256(21696404247141728714962867111982301366100271063999820241464871326479977256901), uint256(9661378036765167190425808584779874801840746805682617740803393856670237423001));   
        vk.IC[13] = Pairing.G1Point(uint256(5583816490624438651942181423468243698565051788774593221138799284928302983170), uint256(10553841748671207770884895734639718413138782274554364058491123603624183454969));   
        vk.IC[14] = Pairing.G1Point(uint256(9447993284792159067487840764055567872398498158128904319530399194275833197896), uint256(9940998728442022925333169996015628776674353728589524296308535441498343984000));   
        vk.IC[15] = Pairing.G1Point(uint256(18575814503896437240850754340236423796003710634843889541607295346722846858514), uint256(14117786076214368001717072987491573020441571458348653843337130257888836236525));
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
