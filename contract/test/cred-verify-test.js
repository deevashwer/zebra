const zebra = artifacts.require("ZebraCore")

const {assert} = require('chai')
const fs = require('fs')

const bn = require('bn.js')
const ethers = require('ethers')
const { sign } = require('crypto')

proofObj = JSON.parse(fs.readFileSync('./test/data/CredVerify_proof.json'))
witnessObj = JSON.parse(fs.readFileSync('./test/data/CredVerify_witness.json'))

const privateKey = "4b365dd7042f232ab45bbc5219365ec2847825884d511b1704aa6cebb6fa785f";

// PARSE INPUT
for (let i = 0; i < proofObj.a.length; i++) {
    proofObj.a[i] = new bn(proofObj.a[i])
}
for (let i = 0; i < proofObj.b.length; i++) {
    for (let k = 0; k < proofObj.b[i].length; k++) {
        proofObj.b[i][k] = new bn(proofObj.b[i][k])
    }
}
for (let i = 0; i < proofObj.c.length; i++) {
    proofObj.c[i] = new bn(proofObj.c[i])
}
for (let i = 0; i < witnessObj.length; i++) {
    witnessObj[i] = new bn(witnessObj[i])
}

contract("ZEBRA Credential Verification", async (accounts) => {
    const account = accounts[0];
    let instance;

    let PkCA = [witnessObj[0], witnessObj[1]]
    let auditorPks = [witnessObj[2], witnessObj[3], witnessObj[4], witnessObj[5], witnessObj[6], witnessObj[7], witnessObj[8], witnessObj[9], witnessObj[10], witnessObj[11]]
    let RT_root = witnessObj[12]
    // tokens represents the user-specific tokens (alpha, gamma)
    let tokens = []
    tokens.push((new bn(1)).toString())
    tokens.push((new bn(2)).toString())
    tokens.push((new bn(3)).toString())
    tokens.push((new bn(4)).toString())
    tokens.push((new bn(5)).toString())
    tokens.push((new bn(6)).toString())
    tokens.push((new bn(7)).toString())
    tokens.push((new bn(8)).toString())
    tokens.push((new bn(9)).toString())
    tokens.push((new bn(10)).toString())
    
    let hashed_data = ethers.ethers.solidityPackedSha256(['uint256', 'uint256', 'uint256', 'uint256', 'uint256', 'uint256', 'uint256', 'uint256', 'uint256', 'uint256'], [tokens[0], tokens[1], tokens[2], tokens[3], tokens[4], tokens[5], tokens[6], tokens[7], tokens[8], tokens[9]])
    let signature = await web3.eth.accounts.sign(hashed_data, privateKey)

    // convert hex string to bn
    let hashed_data_bn = new bn(hashed_data.slice(2), 16)
    console.log("Hash: " + hashed_data_bn)
    console.log("Hash (first 128 bits): " + hashed_data_bn.shrn(128))
    console.log("Hash (last 128 bits): " + hashed_data_bn.maskn(128))
    let account_bn = new bn(account.slice(2), 16)
    console.log("account: " + account_bn)

    beforeEach(async () => {
        instance = await zebra.new({from: account})
        await instance.updateCAKeys(PkCA)
        await instance.updateAuditorsPublicKey(auditorPks)
        await instance.updateRevocationList(RT_root)
    })

    it ("should verify credential verification proof", async () => {
        // assert badge doesn't exist before
        const badgeBefore = await instance.badgeVerification(account);
        assert(!badgeBefore)

        const result = await instance.credentialVerification(proofObj.a, proofObj.b, proofObj.c, tokens, account, signature.v, signature.r, signature.s);
        console.log("Gas estimate for core verification: " + result.receipt.gasUsed)

        // assert badge should exist after
        const badgeAfter = await instance.badgeVerification(account);
        assert(badgeAfter)
    }).timeout(0)
})