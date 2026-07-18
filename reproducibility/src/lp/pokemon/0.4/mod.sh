#!/bin/bash

# Loop through all s*/v* subdirectories
for dir in ./s*/v*; do
    [ -d "$dir" ] || continue

    echo "Processing $dir"

    # Rename train-bk-*.lp -> bk.pl
    for f in "$dir"/train-bk-*.lp; do
        [ -e "$f" ] || continue
        mv "$f" "${dir}/bk.pl"
    done

    # Rename train-gt-*.lp -> exs.pl
    for f in "$dir"/train-gt-*.lp; do
        [ -e "$f" ] || continue
        mv "$f" "${dir}/exs.pl"
    done

    # Rename test-bk-*.lp -> test-bk.lp
    for f in "$dir"/test-bk-*.lp; do
        [ -e "$f" ] || continue
        mv "$f" "${dir}/test-bk.lp"
    done

    # Rename test-gt-*.lp -> test-gt.lp
    for f in "$dir"/test-gt-*.lp; do
        [ -e "$f" ] || continue
        mv "$f" "${dir}/test-gt.lp"
    done

done