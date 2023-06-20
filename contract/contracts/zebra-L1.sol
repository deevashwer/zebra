pragma solidity ^0.8.0;

// SPDX-License-Identifier: MIT

import "./Pairing.sol";

contract ZebraL1 {
    using Pairing for *;
    address private owner = msg.sender;

    uint256[2] public PkCA; // Merkle Root for CA's verification keys
    uint256[10] public PkA; // Auditor's public key
    uint256 public RT_ROOT; // Merkle Root for CA's revocation roots
    Pairing.G1Point[2] preprocessedStaticInputs; // Preprocessed static inputs to SNARK [64, 512]
    mapping(address => int) public accessBadgeMap; // accessBadgeMap[address] = 1 if wallet has access; accessBadgeMap[address] = -1 if token is cached
    mapping(address => bytes32) public tokensHashCache; // Map from wallet address to nu = CRH(alpha, gamma)

    function updateRevocationList(uint256 newRoot) public restricted {
        RT_ROOT = newRoot;
        updatePreprocessedStaticInputs();
    }

    function updateCAKeys(uint256[2] calldata _PkCA) public restricted {
        PkCA = _PkCA;
    }

    function updateAuditorsPublicKey(uint256[10] calldata _PkA)
        public
        restricted
    {
        PkA = _PkA;
    }

    function updatePreprocessedStaticInputs() public {
        BatchVerifyingKey[2] memory bvk = [batch64VerifyingKey(), batch512VerifyingKey()];

        for (uint256 i = 0; i < 2; i++) {
            // Compute the linear combination bvk_x
            Pairing.G1Point memory bvk_x = Pairing.G1Point(0, 0);

            bvk_x = Pairing.plus(bvk_x, bvk[i].IC[0]);
            bvk_x = Pairing.plus(bvk_x, Pairing.scalar_mul(bvk[i].IC[1], PkCA[0]));
            bvk_x = Pairing.plus(bvk_x, Pairing.scalar_mul(bvk[i].IC[2], PkCA[1]));
            bvk_x = Pairing.plus(bvk_x, Pairing.scalar_mul(bvk[i].IC[3], PkA[0]));
            bvk_x = Pairing.plus(bvk_x, Pairing.scalar_mul(bvk[i].IC[4], PkA[1]));
            bvk_x = Pairing.plus(bvk_x, Pairing.scalar_mul(bvk[i].IC[5], PkA[2]));
            bvk_x = Pairing.plus(bvk_x, Pairing.scalar_mul(bvk[i].IC[6], PkA[3]));
            bvk_x = Pairing.plus(bvk_x, Pairing.scalar_mul(bvk[i].IC[7], PkA[4]));
            bvk_x = Pairing.plus(bvk_x, Pairing.scalar_mul(bvk[i].IC[8], PkA[5]));
            bvk_x = Pairing.plus(bvk_x, Pairing.scalar_mul(bvk[i].IC[9], PkA[6]));
            bvk_x = Pairing.plus(bvk_x, Pairing.scalar_mul(bvk[i].IC[10], PkA[7]));
            bvk_x = Pairing.plus(bvk_x, Pairing.scalar_mul(bvk[i].IC[11], PkA[8]));
            bvk_x = Pairing.plus(bvk_x, Pairing.scalar_mul(bvk[i].IC[12], PkA[9]));
            bvk_x = Pairing.plus(bvk_x, Pairing.scalar_mul(bvk[i].IC[13], RT_ROOT));

            preprocessedStaticInputs[i] = bvk_x;
        }
    }

    function badgeVerification(address addr) public view returns (bool) {
        return accessBadgeMap[addr] == 1;
    }

    function resetBadge(address addr) public {
        accessBadgeMap[addr] = -1;
    }

    function resetTokens(address addr) public {
        tokensHashCache[addr] = 0;
        accessBadgeMap[addr] = 0;
    }

    function splitInt(uint256 input) public pure returns (uint256[2] memory) {
        return [input >> 128, (input & (2**128 - 1))];
    }

    function batchedL1VerificationInit(
        address[] calldata addrs,
        uint256[] calldata tokens, //  10 each
        uint8[] calldata _v,
        bytes32[] calldata _r,
        bytes32[] calldata _s,
        uint256 numUsers
    ) public {
        for (uint256 i = 0; i < numUsers; i++) {
            bytes32 hashedMessage = sha256(abi.encodePacked(tokens[i*10:(i+1)*10]));
            {
                bytes32 doubleHashedMessage = keccak256(
                    abi.encodePacked(
                        "\x19Ethereum Signed Message:\n32",
                        hashedMessage
                    )
                );

                require(
                    verifySignature(doubleHashedMessage, _v[i], _r[i], _s[i]) == addrs[i],
                    "Signatures should verify"
                );
            }
            tokensHashCache[addrs[i]] = hashedMessage;
            accessBadgeMap[addrs[i]] = -1;
        }
    }

    function batchedL1VerificationCached(
        uint256[2] calldata a,
        uint256[2][2] calldata b,
        uint256[2] calldata c,
        address[] calldata addrs,
        uint256 numUsers
    ) public {
        uint256 start = 0;
        bytes32 allHashedMessages = sha256(abi.encodePacked(start));

        for (uint256 i = 0; i < numUsers; i++) {
            address addr = addrs[i];
            bytes32 hashedMessage = tokensHashCache[addr];
            bytes memory packedMessage = abi.encodePacked(addr, hashedMessage, allHashedMessages);
            allHashedMessages = sha256(packedMessage);
            accessBadgeMap[addr] = 1;
        }
        Pairing.G1Point memory bvk_x = processUserSNARKInputs(
            splitInt(uint256(allHashedMessages)), numUsers
        );
        require(
            batchVerifyProofs(a, b, c, bvk_x, numUsers),
            "Batch Verification Proof should verify"
        );
    }

    function verifySignature(
        bytes32 _hashedMessage,
        uint8 _v,
        bytes32 _r,
        bytes32 _s
    ) public pure returns (address) {
        address signer = ecrecover(_hashedMessage, _v, _r, _s);
        return signer;
    }

    uint256 constant SNARK_SCALAR_FIELD =
        21888242871839275222246405745257275088548364400416034343698204186575808495617;
    uint256 constant PRIME_Q =
        21888242871839275222246405745257275088696311157297823662689037894645226208583;

    struct BatchVerifyingKey {
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

    function batch64VerifyingKey()
        internal
        pure
        returns (BatchVerifyingKey memory vk)
    {
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

    function batch512VerifyingKey()
        internal
        pure
        returns (BatchVerifyingKey memory vk)
    {
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

    function processUserSNARKInputs(uint256[2] memory input, uint256 numUsers)
        public
        view
        returns (Pairing.G1Point memory vk_x)
    {
        require(numUsers == 64 || numUsers == 512, "numUsers must be 64 or 512");
        BatchVerifyingKey memory bvk = numUsers == 64 ? batch64VerifyingKey() : batch512VerifyingKey();

        Pairing.G1Point memory _bvk_x = Pairing.G1Point(0, 0);

        for (uint256 i = 0; i < input.length; i++) {
            require(
                input[i] < SNARK_SCALAR_FIELD,
                "verifier-gte-snark-scalar-field"
            );
            _bvk_x = Pairing.plus(
                _bvk_x,
                // first 1 + 13 inputs are common to all users and already preprocessed
                Pairing.scalar_mul(bvk.IC[i + 14], input[i])
            );
        }
        return _bvk_x;
    }

    function batchVerifyProofs(
        uint256[2] calldata a,
        uint256[2][2] calldata b,
        uint256[2] calldata c,
        Pairing.G1Point memory bvk_x,
        uint256 numUsers
    ) public view returns (bool r) {
        Proof memory proof;
        proof.A = Pairing.G1Point(a[0], a[1]);
        proof.B = Pairing.G2Point([b[0][0], b[0][1]], [b[1][0], b[1][1]]);
        proof.C = Pairing.G1Point(c[0], c[1]);

        BatchVerifyingKey memory bvk = numUsers == 64 ? batch64VerifyingKey() : batch512VerifyingKey();

        // Make sure that proof.A, B, and C are each less than the prime q
        require(proof.A.X < PRIME_Q, "verifier-aX-gte-prime-q");
        require(proof.A.Y < PRIME_Q, "verifier-aY-gte-prime-q");

        require(proof.B.X[0] < PRIME_Q, "verifier-bX0-gte-prime-q");
        require(proof.B.Y[0] < PRIME_Q, "verifier-bY0-gte-prime-q");

        require(proof.B.X[1] < PRIME_Q, "verifier-bX1-gte-prime-q");
        require(proof.B.Y[1] < PRIME_Q, "verifier-bY1-gte-prime-q");

        require(proof.C.X < PRIME_Q, "verifier-cX-gte-prime-q");
        require(proof.C.Y < PRIME_Q, "verifier-cY-gte-prime-q");

        Pairing.G1Point memory preprocessedInputs = (numUsers == 64) ? preprocessedStaticInputs[0] : preprocessedStaticInputs[1];
        bvk_x = Pairing.plus(bvk_x, preprocessedInputs);

        return
            Pairing.pairing(
                Pairing.negate(proof.A),
                proof.B,
                bvk.alfa1,
                bvk.beta2,
                bvk_x,
                bvk.gamma2,
                proof.C,
                bvk.delta2
            );
    }

    modifier restricted() {
        require(
            msg.sender == owner,
            "This function is restricted to the contract's owner"
        );
        _;
    }
}
