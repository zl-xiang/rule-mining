#!/bin/bash

# Iterate through all .log files in current directory
for file in *.log
do
    # Skip if no .log files exist
    [ -e "$file" ] || continue

    # Output file with .lp suffix
    output="${file%.log}.lp"

    # Keep only lines AFTER the separator line
    sed '1,/^\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*$/d' \
        "$file" > "$output"

    echo "Generated: $output"
done