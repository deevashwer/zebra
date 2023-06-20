#!/bin/bash

if [ $# -ne 1 ]; then
    echo "Usage: dummyContractCircuits.sh <contractName>\n<contractName> Options: {CredVerify, BatchL1-64, BatchL2-64, BatchL1-512, BatchL2-512}"
    exit 1
fi

echo "creating proof"
cd dummyVerify
go build -ldflags="-X 'main.ProtocolName=$1'" -o dummyVerify
./dummyVerify
rm dummyVerify
cd ..
echo "massaging proof for contract tests"
node convertOutput.js $1
echo "removing unnecessary files"
cd dummyVerify
rm $1.proof $1.witness
echo "the verification key for this contract is available in dummyVerify/$1.sol; please copy it to the appropriate contract"