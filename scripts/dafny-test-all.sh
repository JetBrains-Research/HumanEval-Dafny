#!/bin/bash

# This script runs all dafny tests in the current directory.

for f in *.dfy
do
    echo "Testing $f"
    dafny verify --verification-time-limit 10 $f
done
