#!/bin/bash

SIM_FILE="./sim.lp"

# Check that sim.lp exists
if [ ! -f "$SIM_FILE" ]; then
    echo "Error: $SIM_FILE not found"
    exit 1
fi

# Find all v{int} directories
find . -type d | grep -E '/v[0-9]+$' | while read -r dir; do
    echo "Processing $dir"

    for f in bk.pl test-bk.lp; do
        target="$dir/$f"

        if [ -f "$target" ]; then
            echo "Appending to $target"
            cat "$SIM_FILE" >> "$target"
        else
            echo "Skipping (not found): $target"
        fi
    done
done