const zebra = artifacts.require("ZebraL1")

const {assert} = require('chai')
const fs = require('fs')

const bn = require('bn.js')
const ethers = require('ethers')

const HDWalletProvider = require("@truffle/hdwallet-provider")

const mnemonicPhrase = "license gasp silver butter memory arctic faculty major story length bean believe index lift engage"

const provider = new HDWalletProvider({
    mnemonic: {
      phrase: mnemonicPhrase
    },
    numberOfAddresses: 512,
    providerOrUrl: "http://localhost:7545"
})

generatedAccounts = [];

for (let i = 0; i < 512; i++) {
    let address = provider.addresses[i].toString("hex")
    generatedAccounts.push([address, provider.wallets[address].privateKey.toString("hex")])
}

batchProofObj = JSON.parse(fs.readFileSync('./test/data/BatchL1-512_proof.json'))
batchWitnessObj = JSON.parse(fs.readFileSync('./test/data/BatchL1-512_witness.json'))
// PARSE INPUT
for (let i = 0; i < batchProofObj.a.length; i++) {
    batchProofObj.a[i] = new bn(batchProofObj.a[i])
}
for (let i = 0; i < batchProofObj.b.length; i++) {
    for (let k = 0; k < batchProofObj.b[i].length; k++) {
        batchProofObj.b[i][k] = new bn(batchProofObj.b[i][k])
    }
}
for (let i = 0; i < batchProofObj.c.length; i++) {
    batchProofObj.c[i] = new bn(batchProofObj.c[i])
}
for (let i = 0; i < batchWitnessObj.length; i++) {
    batchWitnessObj[i] = new bn(batchWitnessObj[i])
}

batchProofObj_64 = JSON.parse(fs.readFileSync('./test/data/BatchL1-64_proof.json'))
batchWitnessObj_64 = JSON.parse(fs.readFileSync('./test/data/BatchL1-64_witness.json'))
// PARSE INPUT
for (let i = 0; i < batchProofObj_64.a.length; i++) {
    batchProofObj_64.a[i] = new bn(batchProofObj_64.a[i])
}
for (let i = 0; i < batchProofObj_64.b.length; i++) {
    for (let k = 0; k < batchProofObj_64.b[i].length; k++) {
        batchProofObj_64.b[i][k] = new bn(batchProofObj_64.b[i][k])
    }
}
for (let i = 0; i < batchProofObj_64.c.length; i++) {
    batchProofObj_64.c[i] = new bn(batchProofObj_64.c[i])
}
for (let i = 0; i < batchWitnessObj_64.length; i++) {
    batchWitnessObj_64[i] = new bn(batchWitnessObj_64[i])
}

contract("ZEBA Batch L1 Verification", async (accounts) => {
    let maxUsers = 512;
    const account = accounts[0];
    let instance;

    let addresses = []
    let tokens = []
    let prehashed = []
    let v = []
    let r = []
    let s = []
    let finalHash = ethers.ethers.solidityPackedSha256(['uint256'], [0])
    let finalHash_64;

    for (let i = 0; i < maxUsers; i++) {
        addresses.push(generatedAccounts[i][0])

        tokens.push((new bn(i+1)).toString())
        tokens.push((new bn(i+2)).toString())
        tokens.push((new bn(i+3)).toString())
        tokens.push((new bn(i+4)).toString())
        tokens.push((new bn(i+5)).toString())
        tokens.push((new bn(i+6)).toString())
        tokens.push((new bn(i+7)).toString())
        tokens.push((new bn(i+8)).toString())
        tokens.push((new bn(i+9)).toString())
        tokens.push((new bn(i+10)).toString())
        
        let data =       
        ethers.ethers.solidityPackedSha256(
            ['uint256', 'uint256', 'uint256', 'uint256', 'uint256', 'uint256', 'uint256', 'uint256', 'uint256', 'uint256'],
                [tokens[i*10],
                tokens[i*10+1],
                tokens[i*10+2],
                tokens[i*10+3],
                tokens[i*10+4],
                tokens[i*10+5],
                tokens[i*10+6],
                tokens[i*10+7],
                tokens[i*10+8],
                tokens[i*10+9]])

        let signature = await web3.eth.accounts.sign(data, generatedAccounts[i][1])

        prehashed.push(data)

        finalHash = ethers.ethers.solidityPackedSha256(['address', 'bytes32', 'bytes32'], [addresses[i], data, finalHash])

        if (i == 63) {
            finalHash_64 = finalHash;
        }

        v.push(signature.v)
        r.push(signature.r)
        s.push(signature.s)
    }
    // convert hex string to bn
    let finalHash_bn = new bn(finalHash.slice(2), 16)
    let finalHash_64_bn = new bn(finalHash_64.slice(2), 16)
    console.log("Final Hash 512: " + finalHash_bn)
    console.log("Final Hash 512 (first 128 bits): " + finalHash_bn.shrn(128))
    console.log("Final Hash 512 (last 128 bits): " + finalHash_bn.maskn(128))
    console.log("Final Hash 64: " + finalHash_64_bn)
    console.log("Final Hash 64 (first 128 bits): " + finalHash_64_bn.shrn(128))
    console.log("Final Hash 64 (last 128 bits): " + finalHash_64_bn.maskn(128))

    function batchTest(N) {

        let PkCA;
        let auditorPks;
        let RT_root;
        let finalHash_one;
        let finalHash_two;

        let activeProofObj;

        if (N == 512) {
            PkCA = [batchWitnessObj[0], batchWitnessObj[1]]
            auditorPks = [batchWitnessObj[2], batchWitnessObj[3], batchWitnessObj[4], batchWitnessObj[5], batchWitnessObj[6],
             batchWitnessObj[7], batchWitnessObj[8], batchWitnessObj[9], batchWitnessObj[10], batchWitnessObj[11]]
            RT_root = batchWitnessObj[12]
            finalHash_one = batchWitnessObj[13]
            finalHash_two = batchWitnessObj[14]

            activeProofObj = batchProofObj;
        } else if (N==64) {
            PkCA = [batchWitnessObj_64[0], batchWitnessObj_64[1]]
            auditorPks = [batchWitnessObj_64[2], batchWitnessObj_64[3], batchWitnessObj_64[4], batchWitnessObj_64[5], batchWitnessObj_64[6],
            batchWitnessObj_64[7], batchWitnessObj_64[8], batchWitnessObj_64[9], batchWitnessObj_64[10], batchWitnessObj_64[11]]
            RT_root = batchWitnessObj_64[12]
            finalHash_one = batchWitnessObj_64[13]
            finalHash_two = batchWitnessObj_64[14]

            activeProofObj = batchProofObj_64;
        } else {
            return;
        }

        beforeEach(async () => {
            instance = await zebra.new({from: account})
            await instance.updateCAKeys(PkCA)
            await instance.updateAuditorsPublicKey(auditorPks)
            await instance.updateRevocationList(RT_root)
        })

        it ("should verify batch L1 verification init and cached - " + N + " users", async () => {
            let result = await instance.batchedL1VerificationInit(addresses.slice(0, N), tokens.slice(0, 10*N), v.slice(0, N), r.slice(0, N), s.slice(0, N), N);
            console.log("Gas estimate for batch L1 verification init per user (N = " + N + "): " + result.receipt.gasUsed/N)

            // assert badge should NOT exist before
            badge = await instance.badgeVerification(addresses[0]);
            assert(!badge)

            result = await instance.batchedL1VerificationCached(activeProofObj.a, activeProofObj.b, activeProofObj.c, addresses.slice(0, N), N);
            console.log("Gas estimate for batch L1 verification cached per user (N = " + N + "): " + result.receipt.gasUsed/N)

            // assert badge should exist after
            badge = await instance.badgeVerification(addresses[0]);
            assert(badge)
        }).timeout(0);
    }
    batchTest(64);
    batchTest(512); 
})