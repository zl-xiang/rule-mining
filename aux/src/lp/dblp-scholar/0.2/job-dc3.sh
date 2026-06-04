#!/bin/bash

source ~/miniconda3/etc/profile.d/conda.sh

# =========================
# Configuration
# =========================

dataset="dblp-scholar"
sample=(1 2 3 4 5)
sub_sample=(1 2 3 4 5)
split=0.2

# theta_values=(0.5 1 1.5 2 2.5 3 3.5 4)
# delta_values=(1 0.6 0.4 0.25 0.2 0.15 0.1)
theta=0.5
delta=0.025

extra_string="sim(X,X) :- att(T,Attr,X).
sim(X,Y):- sim(Y,X).
:- att(V2,did,X),dblp(V2),scholar(V3), att(V3,sid,Y), eqo(X,Y), att(V2,dtitle,VN1), att(V3,stitle,VN2), not sim(VN1,VN2).
:- att(V2,did,X),dblp(V2),scholar(V3), att(V3,sid,Y), eqo(X,Y), att(V2,dauthors,VN1), att(V3,sauthors,VN2), not sim(VN1,VN2).

#show.
#show (X,Y): att(V2,did,X),dblp(V2),scholar(V3), att(V3,sid,Y), eqo(X,Y), X!=Y.
"

base_dir="./results"
score_file="$base_dir/scores/${dataset}-${split}-s${sample}-dc-scores3.csv"

# Create CSV header
if [ ! -f "$score_file" ]; then
    echo "sample,sub_sample,result_id,test_precision,test_recall,test_f1" \
        > "$score_file"
fi

# =========================
# Main Loop
# =========================

for s in "${sample[@]}"
do
    for v in "${sub_sample[@]}"
    do

        run_name="${dataset}-${split}-s${s}-v${v}-t${theta}-d${delta}"

        raw_log="$base_dir/logs/dc/${run_name}-dc3.log"

        # Original learned rule file
        original_rule_file="$base_dir/rules/${run_name}.lp"

        # Temporary ERA rule file (do NOT alter original)
        era_rule_file="$base_dir/rules/${run_name}-era2.lp"

        # ========================================
        # Create ERA-specific rule file
        # Replace ONLY rule heads:
        # eqo(V0,V1) :- ...
        # ->
        # activeo(V0,V1) :- ...
        # ========================================

        sed -E 's/^eqo\(([^,]+),([^)]*)\)[[:space:]]*:-/activeo(\1,\2) :-/' \
            "$original_rule_file" > "$era_rule_file"

        echo "Generated ERA rule file:"
        echo "$era_rule_file"

        # ========================================
        # Add extra string to ERA rule file
        # ========================================

        tmp_rule_file="${era_rule_file}.tmp"

        {
            echo "$extra_string"
            echo ""
            cat "$era_rule_file"
        } > "$tmp_rule_file"

        mv "$tmp_rule_file" "$era_rule_file"

        echo "Extra rules added."

        conda activate asp_en

        echo "Activated ERA environment"

        # ========================================
        # Run ERA evaluation
        # ========================================

        era_base_dir="/home/zhiliangxiang/Academic/project/lace-asp/ERA/src"
        era_test_dir="${era_base_dir}/experiment/trc-rule/${dataset}/${split}/s${s}"
        era_output_dir="${era_test_dir}/v${v}"

        echo "${era_output_dir}"

        mkdir -p "$era_output_dir"

        era_log="${era_output_dir}/${run_name}-dc3.log"

        python -u \
            ${era_base_dir}/main_lacep.py \
            -l "$era_rule_file" \
            ${era_output_dir}/bias.pl \
            ${era_test_dir}/test-bk.lp \
            ${era_test_dir}/test-gt.lp \
            --trc --opt maxsol --heur --debug -e 50 \
            > "$era_log" 2>&1

        echo "ERA finished."

        # ========================================
        # Extract ALL testing scores
        # ========================================

        echo "Extracting all Results lines..."

        result_id=1

        grep "Results" "$era_log" | while read -r eval_line
        do

            echo "Evaluation line:"
            echo "$eval_line"

            test_precision=$(echo "$eval_line" | grep -oP 'Precision = \K[0-9.]+')
            test_recall=$(echo "$eval_line" | grep -oP 'Recall = \K[0-9.]+')
            test_f1=$(echo "$eval_line" | grep -oP 'F1 = \K[0-9.]+')

            # Skip malformed lines
            if [[ -z "$test_precision" || -z "$test_recall" || -z "$test_f1" ]]; then
                continue
            fi

            # ========================================
            # Append results to CSV
            # ========================================

            echo "${s},${v},${result_id},${test_precision},${test_recall},${test_f1}" \
                >> "$score_file"

            echo "Scores appended for result ${result_id}"

            result_id=$((result_id + 1))

        done

        conda deactivate

    done
done

echo "======================================="
echo "All jobs completed."
echo "======================================="