#!/bin/bash

source ~/miniconda3/etc/profile.d/conda.sh

# =========================
# Configuration
# =========================

dataset="cddb"
sample="4"
split="80"
v="v1"

theta_values=(0.5 0.8 1 1.5 2 3 4)
delta_values=(1 0.8 0.5 0.25 0.1 0.08 0.05 0.025)

extra_string="sim(X,X):- att(T,A,X).
              sim(Y,X):- sim(X,Y).
              eqo(X,X):-att(T,id,X).
              "

base_dir="./results"

mkdir -p "$base_dir/logs"
mkdir -p "$base_dir/rules"
mkdir -p "$base_dir/scores"

score_file="$base_dir/scores/${dataset}-${split}-s${sample}-scores-v1.csv"

# Create CSV header
if [ ! -f "$score_file" ]; then
    echo "theta,delta,popper_time_sec,train_precision,train_recall,tp,fn,tn,fp,rules,size,val_precision,val_recall,val_f1,test_precision,test_recall,test_f1" \
        > "$score_file"
fi

# =========================
# Main Loop
# =========================

for p1 in "${theta_values[@]}"
do
    for p2 in "${delta_values[@]}"
    do

        echo "======================================="
        echo "Running theta=$p1 delta=$p2"
        echo "======================================="

        run_name="${dataset}-${split}-s${sample}-t${p1}-d${p2}"
        v_run_name="${run_name}-${v}"
        raw_log="$base_dir/logs/${run_name}.log"
        rule_file="$base_dir/rules/${run_name}.lp"

        conda activate /home/zhiliangxiang/Academic/project/rule-mining/.rule-mining

        echo "Activated ER rule learning environment"
        # ========================================
        # Run Popper
        # ========================================
        start_time=$(date +%s)

        python /home/zhiliangxiang/Academic/project/rule-mining/rule-mining/popper.py -fp "$p1" -d "$p2" ./ \
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
        era_output_dir="${era_base_dir}/experiment/trc-rule/${dataset}/${split}/s${sample}"
        era_val_dir="${era_output_dir}/${v}"
        echo "${era_output_dir}"
        mkdir -p "$era_output_dir"

        era_val_log="${era_val_dir}/${run_name}-val.log"

        python -u \
            ${era_base_dir}/main_lacep.py \
            -l "$rule_file" \
            ${era_output_dir}/bias.pl \
            ${era_val_dir}/test-bk.lp \
            ${era_val_dir}/test-gt.lp \
            --trc --opt maxsol --heur --debug --no_show --typed_eval \
            > "$era_val_log" 2>&1

        era_log="${era_output_dir}/${v_run_name}.log"

        python -u \
            ${era_base_dir}/main_lacep.py \
            -l "$rule_file" \
            ${era_output_dir}/bias.pl \
            ${era_output_dir}/test-bk.lp \
            ${era_output_dir}/test-gt.lp \
            --trc --opt maxsol --heur --debug --no_show --typed_eval\
            > "$era_log" 2>&1

        echo "ERA finished."

        # ========================================
        # Extract testing scores
        # ========================================

        eval_val_line=$(grep "Results" "$era_val_log" | tail -n 1)

        echo "era_val_log Evaluation line:"
        echo "$eval_val_line"

        val_precision=$(echo "$eval_val_line" | grep -oP 'Precision = \K[0-9.]+')
        val_recall=$(echo "$eval_val_line" | grep -oP 'Recall = \K[0-9.]+')
        val_f1=$(echo "$eval_val_line" | grep -oP 'F1 = \K[0-9.]+')


        eval_line=$(grep "Results" "$era_log" | tail -n 1)

        echo "Evaluation line:"
        echo "$eval_line"

        test_precision=$(echo "$eval_line" | grep -oP 'Precision = \K[0-9.]+')
        test_recall=$(echo "$eval_line" | grep -oP 'Recall = \K[0-9.]+')
        test_f1=$(echo "$eval_line" | grep -oP 'F1 = \K[0-9.]+')

        # ========================================
        # Append ALL results to CSV
        # ========================================

        echo "${p1},${p2},${popper_time},${train_precision},${train_recall},${tp},${fn},${tn},${fp},${rules},${size},${val_precision},${val_recall},${val_f1},${test_precision},${test_recall},${test_f1}" \
            >> "$score_file"

        echo "Scores appended."

    done
done

echo "======================================="
echo "All jobs completed."
echo "======================================="