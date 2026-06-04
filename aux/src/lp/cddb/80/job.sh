#!/bin/bash

source ~/miniconda3/etc/profile.d/conda.sh

# =========================
# Configuration
# =========================

dataset="cddb"
sample=(1 2 3 4 5)
split=80

# theta_values=(0.5 1 1.5 2 2.5 3 3.5 4)
# delta_values=(1 0.6 0.4 0.25 0.2 0.15 0.1)
theta=2
delta=0.15

extra_string="sim(X,X) :- att(T,Attr,X).
sim(X,Y):- sim(Y,X).


#show.
#show (X,Y): att(V2,id,X),cora(V2), cora(V3), att(V3,id,Y), X!=Y, eqo(X,Y)."

base_dir="./results"

mkdir -p "$base_dir/logs"
mkdir -p "$base_dir/rules"
mkdir -p "$base_dir/scores"

score_file="$base_dir/scores/${dataset}-${split}-s${sample}-scores.csv"

# Create CSV header
if [ ! -f "$score_file" ]; then
    echo "sample,popper_time_sec,train_precision,train_recall,tp,fn,tn,fp,rules,size,test_precision,test_recall,test_f1" \
        > "$score_file"
fi

# =========================
# Main Loop
# =========================

for s in "${sample[@]}"
do

    echo "======================================="
    echo "Running theta=$theta delta=$delta"
    echo "======================================="

    run_name="${dataset}-${split}-s${s}-t${theta}-d${delta}"
    raw_log="$base_dir/logs/${run_name}.log"
    rule_file="$base_dir/rules/${run_name}.lp"

    conda activate /home/zhiliangxiang/Academic/project/rule-mining/.rule-mining

    echo "Activated ER rule learning environment"
    # ========================================
    # Run Popper
    # ========================================
    start_time=$(date +%s)

    python /home/zhiliangxiang/Academic/project/rule-mining/rule-mining/popper.py -fp "$theta" -d "$delta" ./s${s} \
        > "$raw_log" 2>&1

    popper_exit=$?

    end_time=$(date +%s)

    popper_time=$((end_time - start_time))

    conda deactivate

    echo "Popper runtime: ${popper_time} sec"
    # ----

    #python /home/zhiliangxiang/Academic/project/rule-mining/rule-mining/popper.py -fp "$p1" -d "$p2" ./ \
    #  > "$raw_log" 2>&1

    #echo "Popper finished."

    # ========================================
    # Extract training scores
    # ========================================

    score_line=$(grep "^Precision:" "$raw_log")

    train_precision=$(echo "$score_line" | grep -oP 'Precision:\K[0-9.]+')
    train_recall=$(echo "$score_line" | grep -oP 'Recall:\K[0-9.]+')
    tp=$(echo "$score_line" | grep -oP 'TP:\K[0-9]+')
    fn=$(echo "$score_line" | grep -oP 'FN:\K[0-9]+')
    tn=$(echo "$score_line" | grep -oP 'TN:\K[0-9]+')
    fp=$(echo "$score_line" | grep -oP 'FP:\K[0-9]+')
    rules=$(echo "$score_line" | grep -oP 'Rules:\K[0-9]+')
    size=$(echo "$score_line" | grep -oP 'Size:\K[0-9]+')

    # ========================================
    # Extract rules
    # ========================================

    awk '/^\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*/ {flag=1; next} flag' \
        "$raw_log" > "$rule_file"

    # ========================================
    # Add extra string
    # ========================================

    tmp_file="${rule_file}.tmp"

    {
        echo "$extra_string"
        echo ""
        cat "$rule_file"
    } > "$tmp_file"

    mv "$tmp_file" "$rule_file"

    echo "Rule file generated:"
    echo "$rule_file"

    conda activate asp_en

    echo "Activated ERA environment"
    # ========================================
    # Run ERA evaluation
    # ========================================
    era_base_dir="/home/zhiliangxiang/Academic/project/lace-asp/ERA/src"
    era_output_dir="${era_base_dir}/experiment/trc-rule/${dataset}/${split}/s${s}"
    echo "${era_output_dir}"
    mkdir -p "$era_output_dir"

    era_log="${era_output_dir}/${run_name}.log"

    python -u \
        ${era_base_dir}/main_lacep.py \
        -l "$rule_file" \
        ${era_output_dir}/bias.pl \
        ${era_output_dir}/test-bk.lp \
        ${era_output_dir}/test-gt.lp \
        --trc --opt maxsol --heur --debug \
        > "$era_log" 2>&1

    echo "ERA finished."

    # ========================================
    # Extract testing scores
    # ========================================

    eval_line=$(grep "Results" "$era_log" | tail -n 1)

    echo "Evaluation line:"
    echo "$eval_line"

    test_precision=$(echo "$eval_line" | grep -oP 'Precision = \K[0-9.]+')
    test_recall=$(echo "$eval_line" | grep -oP 'Recall = \K[0-9.]+')
    test_f1=$(echo "$eval_line" | grep -oP 'F1 = \K[0-9.]+')

    # ========================================
    # Append ALL results to CSV
    # ========================================

    echo "${s},${popper_time},${train_precision},${train_recall},${tp},${fn},${tn},${fp},${rules},${size},${test_precision},${test_recall},${test_f1}" \
        >> "$score_file"

    echo "Scores appended."

done

echo "======================================="
echo "All jobs completed."
echo "======================================="