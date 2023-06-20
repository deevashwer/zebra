#!/bin/bash

if [[ $1 == "CredVerify" ]]; then
    numConstraints=386227
elif [[ $1 == "Aggregator64" ]]; then
    numConstraints=65115858
elif [[ $1 == "Aggregator512" ]]; then
    numConstraints=105344642
else
    echo "Usage: bench_groth16.sh <circuitName>\n<circuitName> Options: {CredVerify, Aggregator64, Aggregator512}"
    exit 1
fi

cd bench_groth16
go build -ldflags="-X 'main.r1csConstraintsString=$numConstraints'" -o bench_groth16
./bench_groth16
rm bench_groth16
