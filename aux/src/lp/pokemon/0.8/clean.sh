#!/bin/bash

# Find only directories named v<number>
find . -type d -regex '.*/v[0-9]+' | while read -r dir; do
    echo "Processing $dir"

    rm -f "$dir/spec_desc.csv"
    rm -f "$dir/species_dups.csv"
    rm -f "$dir/species.csv"
    rm -f "$dir/spec_name.csv"
    rm -f "$dir/test-bk.lp"
    rm -f "$dir/test-gt.lp"
    rm -f "$dir/val-bk.lp"
    rm -f "$dir/val-gt.lp"
    rm -f "$dir/bk.pl"
    rm -f "$dir/exs.pl"
done