const fs = require('fs');
const readline = require('readline');

protocol_name = process.argv[2]

proof = fs.createReadStream('./dummyVerify/' + protocol_name + '.proof');

const rl = readline.createInterface({
    input: proof,
    crlfDelay: Infinity
  });

async function processFile() {
    let lines = []

    for await (const line of rl) {
        lines.push(line.replace(/\[+(.*?)\]+/g,"$1"))
      }

    proofObj = {}

    proofObj.a = lines[0].split(" ")

    let b = lines[1].split(" ")
    proofObj.b = [[b[0], b[1]], [b[2], b[3]]]

    proofObj.c = lines[2].split(" ")

    fs.writeFileSync('./contract/test/data/' + protocol_name + '_proof.json', JSON.stringify(proofObj))
}
try {
processFile().catch(console.error)
} catch(err) {
    console.error(err)
}

//Witness
witness = fs.readFileSync('./dummyVerify/' + protocol_name + '.witness').toString();

witness = witness.split(']')

witness[0] = witness[0].substring(3).split(',')
witness[0].splice(witness[0].length - 1)
witness = witness[0]

fs.writeFileSync('./contract/test/data/' + protocol_name + '_witness.json', JSON.stringify(witness))
