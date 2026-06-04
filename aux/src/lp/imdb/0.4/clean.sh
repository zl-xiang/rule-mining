#!/bin/bash

# Find only directories named v<number>
find . -type d -regex '.*/v[0-9]+' | while read -r dir; do
    echo "Processing $dir"

    rm -f "$dir/title_akas.csv"
    rm -f "$dir/title_basics_dups.csv"
    rm -f "$dir/title_ratings.csv"
    rm -f "$dir/title_basics.csv"
    rm -f "$dir/test-bk.lp"
    rm -f "$dir/test-gt.lp"
    rm -f "$dir/bk.pl"
    rm -f "$dir/exs.pl"
done