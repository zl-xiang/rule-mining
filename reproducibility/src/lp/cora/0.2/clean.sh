#!/bin/bash

# Find only directories named v<number>
find . -type d -regex '.*/v[0-9]+' | while read -r dir; do
    echo "Processing $dir"

    rm -f "$dir/cora_DPL.csv"
    rm -f "$dir/cora.csv"
    rm -f "$dir/test-bk.lp"
    rm -f "$dir/test-gt.lp"
    rm -f "$dir/bk.pl"
    rm -f "$dir/exs.pl"
done