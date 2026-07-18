#!/bin/bash

# Loop through all s*/v* subdirectories
for dir in ./s*/v*; do
    [ -d "$dir" ] || continue

    echo "Processing $dir"

    # Rename test-bk-*.lp -> test-bk.lp
    for f in "$dir"/test-bk.lp; do
        [ -e "$f" ] || continue
        mv "$f" "${dir}/val-bk.lp"
    done

    # Rename test-gt-*.lp -> test-gt.lp
    for f in "$dir"/test-gt.lp; do
        [ -e "$f" ] || continue
        mv "$f" "${dir}/val-gt.lp"
    done

done