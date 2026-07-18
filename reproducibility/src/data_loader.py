from schema_info import Schema, Attribute, Relation, LACE_P
import utils
from typing import List, Tuple, Union
from trans_utils import EQO_PRED, EQV_PRED
import trans_utils
import dataloader
import random
import csv
import os
import csv
import random
from collections import defaultdict
from typing import List, Tuple, Dict, Callable, Set
from itertools import product

import pandas as pd
import random
import re
from typing import Set, List
from rapidfuzz import fuzz

POS_EX_PRED = 'pos'
NEG_EX_PRED = 'neg'
EX_PRED = 'example'
DF_EMPTY = 'nan'



def get_default_tup(rel:Relation)-> list:
    # print(rel.name,len(rel.attrs))
    return ['_' for a in rel.attrs]

def add_dom_val(attribute:Attribute,val,ter = False, escape = False):
    if escape:
        val = utils.escape_old(val,attribute.data_type == Attribute.CAT_SEQ) if not utils.is_empty(val) else trans_utils.DF_EMPTY 
    else: 
        val = utils.escape(val,attribute.data_type == Attribute.CAT_SEQ) if not utils.is_empty(val) else trans_utils.DF_EMPTY 
    const_type = [Attribute.NUM, Attribute.IDS]
    # print(attribute.name,attribute.data_type)
    if attribute.data_type not in const_type and val!=trans_utils.DF_EMPTY:
        val = f'"{val}"' #if ter or attribute.type!=Attribute.O_MERGE else f'"{attribute.id}:{val}"'
    if not isinstance(val,str):
        val = str(int(val))
    return val

def escape(val:str):
    if isinstance(val,str):
        # remove_chars = r'[’\!"#%&\'\(\)\*:;<=>?@，。?★、…【】《》？“”‘’！\[\]\^\`\{|\}~]+'
        # val = re.sub(remove_chars, '', val)
        # line_breaks = r'[\n]+'
        # val = re.sub(line_breaks, ' ', val)
        # if cat_seq:
        #     val = re.sub(r'[,]+','-',val)
        # else: 
        #     val = re.sub(r'[,]+','',val)


        return val.replace('"', '').replace("'", "").replace('\\','')
    #.replace('\\','\\\\')
    else:
        return val
    
def is_empty(val:str)->bool:
    val = str(val) if None != val else val
    return (val == None or val == DF_EMPTY or len(val)<1)

def add_dom_val2( val):
    val = escape(val) if not is_empty(val) else DF_EMPTY 
    # print(attribute.name,attribute.data_type)
    if  val!= DF_EMPTY:
        val = f'"{val}"' #if ter or attribute.type!=Attribute.O_MERGE else f'"{attribute.id}:{val}"'
    return val


def load_atombase(schema:Schema) -> set[str]:
        atom_base = set()
        escape = 'poke' in schema.name
        # print('escape', escape)
        #[fixed]: avoid calculating the similarity scores of IDs
        # TODO: [2023-01-23] iterating attr set of the schema instead of instance records?
        for r_name,tbl in schema.tbls.items():
            rel = schema.rel_index(r_name)
            for _,row in tbl.iterrows():
                r_tup = get_default_tup(rel)
                #r_tup = r_tup[1:]
                # [2023-11-23] modified, canel tuple id
                for a_idx,attr_ in enumerate(tbl.columns):
                    if schema.refs !=None and (r_name,attr_) in schema.refs:
                        attr = schema.index_attr(schema.refs[(r_name,attr_)][1],schema.refs[(r_name,attr_)][0])
                    else: 
                        attr = schema.index_attr(attr_,r_name)
                    # TODO: remove condition
                    if attr!=None:
                        #print(attr.name,attr.type)
                        val = add_dom_val(attr,row[attr_],escape=escape)
                        # reflect_eq = ''
                        # if (attr.type == Attribute.MERGE or attr.type == Attribute.O_MERGE) and val != trans_utils.DF_EMPTY:
                        #     #print(val)
                        #     reflect_eq = f'eqo({val},{val}).'
                        # # joins of null are not premitted
                        # elif attr.type == Attribute.V_MERGE:
                        # #and val != trans_utils.DF_EMPTY:
                        #     tid = row['tid']
                        #     v_pos = f'{str(tid)},{str(a_idx)}'
                        #     reflect_eq = f'{trans_utils.EQV_PRED}({v_pos},{v_pos}).'
                        #     proj_fact = f'{trans_utils.PROJ_PRED}({v_pos},{val}).'
                        #     atom_base.add(proj_fact)
                        # #print(a_idx)
                        # atom_base.add(reflect_eq)
                        r_tup[a_idx] = val
                # r_tup = r_tup[1:]
                r_tup_str = ','.join(r_tup)
                r_atom =f'{r_name}({r_tup_str}).'
                atom_base.add(r_atom)
        return atom_base 
    
    
def load_atombase_trc(schema:Schema) -> set[str]:
        atom_base = set()
        escape = 'poke' in schema.name
        # print('escape', escape)
        #[fixed]: avoid calculating the similarity scores of IDs
        # TODO: [2023-01-23] iterating attr set of the schema instead of instance records?
        for r_name,tbl in schema.tbls.items():
            rel = schema.rel_index(r_name)
            for _,row in tbl.iterrows():
                tid = row['tid']
                for a_idx,attr_ in enumerate(tbl.columns):
                    attr = schema.index_attr(attr_,r_name)
                    if attr!=None and attr.name != 'tid':
                        reflect_eq = ''

                        attr_val = add_dom_val(attr,row[attr_],escape=escape)
                        if attr.type == Attribute.O_MERGE and attr_val != trans_utils.DF_EMPTY:
                                reflect_eq = f'eqo({attr_val},{attr_val}).'
                                atom_base.add(reflect_eq)
                        attr_atom = utils.get_atom(f'{rel.name}_{attr.name}',(tid,attr_val))+'.'
                        atom_base.add(attr_atom)
        return atom_base 
 
 #TODO: load positive examples from ground truth
def load_examples(schema:Schema,percent:int=100) -> set[str]:
    examples = set()
    if schema.ground_truth is None:
        return examples
    for gt_name,gt_tbl in schema.ground_truth.items():
        for row in gt_tbl:
            x_attr_str = gt_name.split('_')[0]
            x_attr = schema.index_attr(x_attr_str.split('-')[1],x_attr_str.split('-')[0])
            y_attr_str = gt_name.split('_')[1]
            y_attr = schema.index_attr(y_attr_str.split('-')[1],y_attr_str.split('-')[0])
            x = add_dom_val(x_attr,row[0])
            y = add_dom_val(y_attr,row[1])
            pos_ex = f'{POS_EX_PRED}({EQO_PRED}({x},{y})).'
            examples.add(pos_ex)
            
    n = int(len(examples) * percent / 100)
    return set(random.sample(list(examples), n))
    
def load_trc_atombase(schema:Schema) -> set[str]:
        atom_base = set()
        #[fixed]: avoid calculating the similarity scores of IDs
        escape = 'poke' in schema.name
        for r_name,tbl in schema.tbls.items():
            for _,row in tbl.iterrows():
                #r_tup = r_tup[1:]
                # [2023-11-23] modified, canel tuple id
                for a_idx,attr_ in enumerate(tbl.columns):
                    if schema.refs !=None and (r_name,attr_) in schema.refs:
                        attr = schema.index_attr(schema.refs[(r_name,attr_)][1],schema.refs[(r_name,attr_)][0])
                    else: 
                        attr = schema.index_attr(attr_,r_name)
                    # TODO: remove condition
                    if attr!=None:
                        val = add_dom_val(attr,row[attr_],escape=escape)
                        reflect_eq = ''
                        tid = row['tid']
                        v_pos = f'{str(tid)},{str(attr_)}'
                        if (attr.type == Attribute.MERGE or attr.type == Attribute.O_MERGE) and val != trans_utils.DF_EMPTY:
                            reflect_eq = f'eqo({val},{val}).'
                        # joins of null are not premitted
                        elif attr.type == Attribute.V_MERGE:
                        #and val != trans_utils.DF_EMPTY:
                            reflect_eq = f'{trans_utils.EQV_PRED}({v_pos},{v_pos}).'
                        proj_fact = f'att({v_pos},{val}).'
                        atom_base.add(proj_fact)
                        atom_base.add(reflect_eq)
                r_atom =f'{r_name}({str(tid)}).'
                atom_base.add(r_atom)
        return atom_base 
    
def get_naive_sim (schema:Schema,sim_pairs:dict, with_thresh = False) -> set[str]:
        #print(self.sim_pairs.keys())
        sim_group = {i:k for i,k in enumerate(sim_pairs.keys())}
        # print(sim_group)
        sim_group_const_ = {i:[] for i in sim_group.keys()}
        sim_group_const = {(k,v):[] for k,v in sim_pairs.items()}
        for r_name,tbl in schema.tbls.items():
            rel = schema.rel_index(r_name=r_name)
            for k,v in sim_pairs.items():
                if r_name in k:
                    first_index = k.index(r_name)
                    if first_index == 0:
                        #print('----', g)
                        #print(len(rel.attrs))
                        attr_name = rel.attrs[k[1]].name
                        # unique_const = tbl[attr_name].value_counts(dropna=True)
                        filtered_column = tbl[attr_name].dropna()
                        unique_consts = filtered_column.unique()
                        sim_group_const[(k,v)].append(unique_consts)
                        if r_name in k[2:]:
                            attr_name_2 = rel.attrs[k[3]].name
                            filtered_column2 = tbl[attr_name_2].dropna()
                            unique_consts2 = filtered_column2.unique()
                            sim_group_const[(k,v)].append(unique_consts2)
                    else:
                        attr_name_2 = rel.attrs[k[3]].name
                        filtered_column2 = tbl[attr_name_2].dropna()
                        unique_consts2 = filtered_column2.unique()
                        sim_group_const[(k,v)].append(unique_consts2)
        
        sim_facts = set()
        #print(len(sim_facts))
        for k, v in sim_group_const.items():
            # attr2 = schema.rel_index(k[2]).attrs[k[3]]
            for c1 in v[0]:
                # print(v[0])
                if 'poke' in schema.name:
                    c1 = utils.escape_old(c1) 
                else:
                    c1 = utils.escape(c1) 
                for c2 in v[1]:
                    if 'poke' in schema.name:
                        c2 = utils.escape_old(c2) 
                    else:
                        c2 = utils.escape(c2) 
                    score = utils.sim(c1,c2)
                    thresh = k[1]
                    if not with_thresh:
                        if score>=thresh:
                            sim_facts.add(utils.get_atom_(f'{trans_utils.SIM_PRED}',(f'"{c1}"',f'"{c2}"')))
                            sim_facts.add(utils.get_atom_(f'{trans_utils.SIM_PRED}',(f'"{c2}"',f'"{c1}"')))
                    else:
                        # print(thresh,k,score)
                        ok_score = 0
                        if score>=thresh and score>=95:
                            ok_score = 95
                        elif score>=thresh and score >=90:
                            ok_score = 90
                        elif score>=thresh and score >=85:
                            ok_score = 85
                        if ok_score > 0:
                            sim_facts.add(utils.get_atom_(f'{trans_utils.SIM_PRED}',(f'"{c1}"',f'"{c2}"',{str(ok_score)})))
                            sim_facts.add(utils.get_atom_(f'{trans_utils.SIM_PRED}',(f'"{c2}"',f'"{c1}"', {str(ok_score)})))
                        #sim_facts.add((c1,c2,score))
        return  sim_facts
    
    
    
def csv_to_asp_facts(csv_path: str,encoding = 'utf-8', attr_prefix='') -> set:
    """
    Convert a CSV file into ASP facts.

    - Uses filename (without extension) as relational predicate
    - First column must be tid
    - All attribute values are quoted
    """
    predicate = os.path.splitext(os.path.basename(csv_path))[0]

    facts = []

    with open(csv_path, newline='', encoding=encoding) as f:
        reader = csv.DictReader(f)

        if 'tid' not in reader.fieldnames:
            raise ValueError("CSV must contain a 'tid' column")

        for row in reader:
            tid = row['tid']

            # relational atom
            facts.append(f"{predicate}({tid}).")

            # attribute atoms
            for attr, val in row.items():
                if attr == 'tid':
                    continue
                if attr_prefix:
                    attr = f"{attr_prefix}{attr}"

                # normalize value to string and escape quotes
                val_str = add_dom_val2(str(val))
                if val_str != DF_EMPTY:
                    facts.append(f'att({tid},{attr},{val_str}).')

    return facts
    
def sample_csv_to_asp_facts(
    csv_path: str,
    encoding='utf-8',
    attr_prefix='',
    sample_ratio: float = 1.0,
    gt_att='id',
    sampled_csv_path: str = None
) -> Tuple[set, set, set, set]:
    """
    Convert a CSV file into ASP facts.

    - Uses filename (without extension) as relational predicate
    - First column must be tid
    - All attribute values are quoted
    - Only a percentage of rows are sampled (sample_ratio in [0,1])
    - Sampled training rows are optionally saved to a new CSV file
    """

    if not (0.0 < sample_ratio <= 1.0):
        raise ValueError("sample_ratio must be in (0,1]")

    predicate = os.path.splitext(os.path.basename(csv_path))[0]

    train_facts = set()
    train_object_ids = set()
    test_facts = set()
    test_object_ids = set()

    sampled_rows = []

    with open(csv_path, newline='', encoding=encoding) as f:
        reader = csv.DictReader(f)

        if 'tid' not in reader.fieldnames:
            raise ValueError("CSV must contain a 'tid' column")

        fieldnames = reader.fieldnames

        for row in reader:

            tid = row['tid']

            # sampling decision
            rand = random.random()

            if rand > sample_ratio:
                test_object_ids.add(row[gt_att])

                # relational atom
                test_facts.add(f"{predicate}({tid}).")

            else:
                train_object_ids.add(row[gt_att])

                # relational atom
                train_facts.add(f"{predicate}({tid}).")

                # save sampled training row
                sampled_rows.append(row)

            # attribute atoms
            for attr, val in row.items():
                if attr == 'tid':
                    continue

                asp_attr = f"{attr_prefix}{attr}" if attr_prefix else attr

                val_str = add_dom_val2(str(val))

                if val_str != DF_EMPTY:
                    if rand > sample_ratio:
                        test_facts.add(
                            f'att({tid},{asp_attr},{val_str}).'
                        )
                    else:
                        train_facts.add(
                            f'att({tid},{asp_attr},{val_str}).'
                        )

    # save sampled training rows to CSV
    if sampled_csv_path is not None:
        with open(sampled_csv_path, 'w', newline='', encoding=encoding) as out_f:
            writer = csv.DictWriter(out_f, fieldnames=fieldnames)

            writer.writeheader()
            writer.writerows(sampled_rows)

    return train_facts, train_object_ids, test_facts, test_object_ids



def from_csv_to_asp_facts(
    csv_path: str,
    train_ids,
    test_ids,
    encoding='utf-8',
    attr_prefix='',
    gt_att='id',
    sampled_csv_path: str = None
) -> Tuple[set, set, set, set]:
    """
    Convert a CSV file into ASP facts.

    - Uses filename (without extension) as relational predicate
    - First column must be tid
    - All attribute values are quoted
    - Only a percentage of rows are sampled (sample_ratio in [0,1])
    - Sampled training rows are optionally saved to a new CSV file
    """


    predicate = os.path.splitext(os.path.basename(csv_path))[0]

    train_facts = set()
    train_object_ids = set()
    test_facts = set()
    test_object_ids = set()

    sampled_rows = []

    with open(csv_path, newline='', encoding=encoding) as f:
        reader = csv.DictReader(f)

        if 'tid' not in reader.fieldnames:
            raise ValueError("CSV must contain a 'tid' column")

        fieldnames = reader.fieldnames

        for row in reader:

            tid = row['tid']
            gt_att_val = row[gt_att]
            # sampling decision
            test_flag = gt_att_val in test_ids
            train_flag = gt_att_val in train_ids
            if test_flag:
                
                test_object_ids.add(row[gt_att])

                # relational atom
                test_facts.add(f"{predicate}({tid}).")

            elif train_flag:
                train_object_ids.add(row[gt_att])

                # relational atom
                train_facts.add(f"{predicate}({tid}).")

                # save sampled training row
                sampled_rows.append(row)

            # attribute atoms
            for attr, val in row.items():
                if attr == 'tid':
                    continue

                asp_attr = f"{attr_prefix}{attr}" if attr_prefix else attr

                val_str = add_dom_val2(str(val))

                if val_str != DF_EMPTY:
                    if test_flag:
                        test_facts.add(
                            f'att({tid},{asp_attr},{val_str}).'
                        )
                    elif train_flag:
                        train_facts.add(
                            f'att({tid},{asp_attr},{val_str}).'
                        )

    # save sampled training rows to CSV
    if sampled_csv_path is not None:
        with open(sampled_csv_path, 'w', newline='', encoding=encoding) as out_f:
            writer = csv.DictWriter(out_f, fieldnames=fieldnames)

            writer.writeheader()
            writer.writerows(sampled_rows)

    return train_facts, test_facts

def sample_csv_to_asp_facts_(
    csv_path: str,
    encoding='utf-8',
    attr_prefix='',
    sample_ratio: float = 1.0,
    gt_att='id'
) -> Tuple[set,set,set,set]:
    """
    Convert a CSV file into ASP facts.

    - Uses filename (without extension) as relational predicate
    - First column must be tid
    - All attribute values are quoted
    - Only a percentage of rows are sampled (sample_ratio in [0,1])
    """

    if not (0.0 < sample_ratio <= 1.0):
        raise ValueError("sample_ratio must be in (0,1]")

    predicate = os.path.splitext(os.path.basename(csv_path))[0]

    train_facts = set()
    train_object_ids = set()
    test_facts = set()
    test_object_ids = set()

    with open(csv_path, newline='', encoding=encoding) as f:
        reader = csv.DictReader(f)

        if 'tid' not in reader.fieldnames:
            raise ValueError("CSV must contain a 'tid' column")

        for row in reader:

            tid = row['tid']
            # sampling decision
            rand = random.random()
            if rand > sample_ratio:
                test_object_ids.add(row[gt_att])
                # relational atom
                test_facts.add(f"{predicate}({tid}).")

            else:
                train_object_ids.add(row[gt_att])
                # relational atom
                train_facts.add(f"{predicate}({tid}).")

            # attribute atoms
            for attr, val in row.items():
                if attr == 'tid':
                    continue

                if attr_prefix:
                    attr = f"{attr_prefix}{attr}"

                val_str = add_dom_val2(str(val))

                if val_str != DF_EMPTY:
                    if rand > sample_ratio:
                        test_facts.add(f'att({tid},{attr},{val_str}).')

                    else:
                        train_facts.add(f'att({tid},{attr},{val_str}).')

    return train_facts, train_object_ids, test_facts, test_object_ids
    
def csv_to_eqo_examples(csv_path: str, is_positive: bool, percent) -> str:
    """
    Convert a two-column CSV into ASP pos/neg eqo examples.

    Args:
        csv_path: path to CSV file with exactly two columns
        is_positive: True -> pos(eqo(...)), False -> neg(eqo(...))
    """
    facts = []
    label = "pos" if is_positive else "neg"

    with open(csv_path, newline='', encoding='utf-8') as f:
        reader = csv.reader(f)
        header = next(reader)  # skip header

        if len(header) != 2:
            raise ValueError("CSV must contain exactly two columns")

        for row in reader:
            if len(row) != 2:
                raise ValueError(f"Invalid row (expected 2 values): {row}")

            v1, v2 = row
            v1 = v1.replace('"', '\\"')
            v2 = v2.replace('"', '\\"')

            facts.append(f'{label}(eqo("{v1}","{v2}")).')
            
    n = int(len(facts) * percent / 100)
    return set(random.sample(list(facts), n))


def load_gt_fact(csv_path: str,is_positive = True) -> str:
    """
    Convert a two-column CSV into ASP pos/neg eqo examples.

    Args:
        csv_path: path to CSV file with exactly two columns
        is_positive: True -> pos(eqo(...)), False -> neg(eqo(...))
    """
    facts = []
    label =  "pos" if is_positive else "neg"

    with open(csv_path, newline='', encoding='utf-8') as f:
        reader = csv.reader(f)
        header = next(reader)  # skip header

        if len(header) != 2:
            raise ValueError("CSV must contain exactly two columns")

        for row in reader:
            if len(row) != 2:
                raise ValueError(f"Invalid row (expected 2 values): {row}")

            v1, v2 = row
            v1 = v1.replace('"', '\\"')
            v2 = v2.replace('"', '\\"')

            facts.append(f'{label}("{v1}","{v2}").')
            
    return set(list(facts))

def pick_ground_truth_pairs(
    ground_truth_csv: str,
    entity_set1: set,
    entity_set2: set,
    encoding='utf-8',
    sampled_csv_path: str = None
) -> Set[str]:
    """
    Returns the subset of ground truth pairs such that
    one entity is in entity_set1 and the other is in entity_set2.

    Assumes CSV has columns 'id1' and 'id2'.

    Optionally saves the selected rows to a new CSV file.
    """

    sampled_rows = []
    selected_pairs = set()

    with open(ground_truth_csv, newline='', encoding=encoding) as f:
        reader = csv.reader(f)

        header = next(reader)

        for row in reader:
            a, b = row[0], row[1]

            # check if one entity is in set1 and the other in set2
            if (a in entity_set1 and b in entity_set2):
                sampled_rows.append(row)
                selected_pairs.add((a, b))

    # optionally save sampled rows
    if sampled_csv_path is not None:
        with open(sampled_csv_path, 'w', newline='', encoding=encoding) as out_f:
            writer = csv.writer(out_f)

            writer.writerow(header)
            writer.writerows(sampled_rows)

    selected_pairs = {
        f'pos(eqo("{a}","{b}")).'
        for a, b in selected_pairs
    }

    return selected_pairs

def generate_non_gt_pairs(
    gt_csv_path: str,
    table1_csv_path: str,
    table2_csv_path: str,
    attr_pair: tuple[str, str],
    output_csv_path: str | None = None
    ,encoding="utf-8"
) -> str:
    """
    Generate pairs of attribute values not appearing in ground truth,
    excluding both (v1, v2) and its symmetric (v2, v1).

    Args:
        gt_csv_path: CSV with two columns (ground truth pairs)
        table1_csv_path: CSV for table 1
        table2_csv_path: CSV for table 2
        attr_pair: (attr_from_table1, attr_from_table2)
        output_csv_path: optional output CSV file path

    Returns:
        CSV string of non-ground-truth pairs
    """
    attr1, attr2 = attr_pair

    # ----------------------------
    # Load ground truth pairs
    # ----------------------------
    gt_pairs = set()
    with open(gt_csv_path, newline='', encoding='utf-8') as f:
        reader = csv.reader(f)
        next(reader)  # skip header
        for row in reader:
            # print(row)
            if len(row) != 2:
                raise ValueError("Ground truth CSV must have exactly two columns")
            v1, v2 = row
            gt_pairs.add((v1, v2))
            gt_pairs.add((v2, v1))  # add symmetry explicitly

    # ----------------------------
    # Load attribute values
    # ----------------------------
    def load_attr_values(csv_path, attr_name):
        values = set()
        with open(csv_path, newline='', encoding=encoding) as f:
            reader = csv.DictReader(f)
            if attr_name not in reader.fieldnames:
                raise ValueError(f"Attribute '{attr_name}' not found in {csv_path}")
            for row in reader:
                values.add(row[attr_name])
        return values

    vals1 = load_attr_values(table1_csv_path, attr1)
    vals2 = load_attr_values(table2_csv_path, attr2)

    # ----------------------------
    # Generate non-GT pairs
    # ----------------------------
    non_gt_pairs = [
        (v1, v2)
        for v1, v2 in product(vals1, vals2)
        if (v1, v2) not in gt_pairs and v1!=v2
    ]

    # ----------------------------
    # Output CSV
    # ----------------------------
    output_lines = [f"{attr1},{attr2}"]
    output_lines += [f"{v1},{v2}" for v1, v2 in non_gt_pairs]
    output_csv = "\n".join(output_lines)

    if output_csv_path:
        with open(output_csv_path, "w", encoding=encoding, newline="") as f:
            f.write(output_csv)

    return output_csv


def sample_negative_examples(
    positive_pairs: Set[str],   # <-- now a set of ASP strings
    table1_csv: str,
    table2_csv: str,
    attr_pairs: List[Tuple[str, str, float]] | None,
    size: int,
    m: int,
    sim: Callable[[str, str], bool],
    encoding='utf-8',
    sim_defined : Set[tuple]  = None,
    index_col = 'id'
) -> Set[str]:
    """
    Synthesise negative examples under attribute-level constraints.

    Negative pairs are generated by recombining elements appearing
    in positive pairs but excluding the true positive pairings.

    Input format:
        pos(eqo("v1","v2")).
    """

    # --------------------------------------------------
    # Parse positive ASP facts
    # --------------------------------------------------
    import re
    pattern = re.compile(r'pos\(eqo\("(.+?)","(.+?)"\)\)\.')

    positives = set()
    for s in positive_pairs:
        mobj = pattern.match(s.strip())
        if mobj:
            positives.add((mobj.group(1), mobj.group(2)))

    # --------------------------------------------------
    # Load tables indexed by attribute values
    # --------------------------------------------------
    def load_table(csv_path):
        with open(csv_path, newline='', encoding=encoding) as f:
            reader = csv.DictReader(f)
            rows = list(reader)
            headers = reader.fieldnames
        return rows, headers

    table1, headers1 = load_table(table1_csv)
    table2, headers2 = load_table(table2_csv)

    # --------------------------------------------------
    # Default attribute pairs
    # --------------------------------------------------
    if attr_pairs is None:
        skip = {"tid", "id"}
        common_attrs = (set(headers1) & set(headers2)) - skip
        attr_pairs = [(a, a, 1.0) for a in common_attrs]
    attr_pairs = list(sorted(attr_pairs, key=lambda x: x[2], reverse=True))
    attrs, weights = zip(*[((a1, a2), w) for a1, a2, w in attr_pairs])
    sampled_cnt_dict = {(a1,a2):0  for (a1,a2) in attrs}
    length_dict = {(a1,a2):int(w*size) for a1, a2, w in attr_pairs}
    
    # --------------------------------------------------
    # Build value → records index
    # --------------------------------------------------
    def build_index(table):
        index = defaultdict(list)
        for row in table:
            for v in row.values():
                index[v].append(row)
        return index

    index1 = build_index(table1)
    # print(index1)
    index2 = build_index(table2)

    # --------------------------------------------------
    # Build candidate negatives from recombination
    # --------------------------------------------------
    left_vals = {v1 for v1, _ in positives}
    right_vals = {v2 for _, v2 in positives}

    candidates = [
        (v1, v2)
        for v1 in left_vals
        for v2 in right_vals
        if (v1, v2) not in positives
    ]

    random.shuffle(candidates)

    # --------------------------------------------------
    # Sampling loop
    # --------------------------------------------------
    results = set()
    attrs = list(attrs)
    weights = list(weights)
    # print(size, length_dict)
    for v1, v2 in candidates:
        #print(sampled_cnt_dict)
        if len(results) >= size:
            break
        for attp in attrs:
            if sampled_cnt_dict[attp] >= length_dict[attp]:
                idx = attrs.index(attp)
                attrs.remove(attp)
                weights.pop(idx)
        recs1 = index1.get(v1)
        #print('11111',recs1)
        recs2 = index2.get(v2)
        #print('22222',recs2)

        if not recs1 or not recs2:
            continue

        r1 = random.choice(recs1)
        r2 = random.choice(recs2)
        #print('11111',r1)
        #print('22222',r2)
        # chosen_attrs = random.choices(attrs, weights=weights, k=m)
        picked = False
        for i, (a1,a2) in enumerate(attrs):
            if picked:
                break
            # passed = True
            val1 = r1.get(a1)
            val2 = r2.get(a2)

            if utils.is_empty(val1) or utils.is_empty(val2):
                #passed = False
                continue

            if random.random() >= 0.8 and (a1,a2) in sim_defined:
                if not sim(val1, val2):
                    #passed = False
                    continue

                sampled_cnt_dict[(a1,a2)]+=1
                picked = True
                print(a1,a2, f'sim sampled {v1},{v2}')

            else:
                if val1 != val2:
                    #passed = False
                    continue
                sampled_cnt_dict[(a1,a2)]+=1
                picked = True
                print(a1,a2, f'eq sampled {v1},{v2}')
        if picked :
            results.add(f'neg(eqo("{v1}","{v2}")).')        

    return results


def sample_negative_examples4(
    positive_pairs: Set[str],
    table1_csv: str,
    table2_csv: str,
    entity_attrs: Tuple[str, str],   # <-- NEW
    attr_pairs: List[Tuple[str, str, float]] | None,
    size: int,
    m: int,
    sim: Callable[[str, str], bool],
    encoding='utf-8',
    sim_defined : Set[tuple]  = None,
) -> Set[str]:
    """
    Negative pairs are generated by recombining entity values taken
    from specified attributes of the two tables.
    """

    # --------------------------------------------------
    # Parse positive ASP facts
    # --------------------------------------------------
    pattern = re.compile(r'pos\(eqo\("(.+?)","(.+?)"\)\)\.')

    positives = set()
    for s in positive_pairs:
        mobj = pattern.match(s.strip())
        if mobj:
            positives.add((mobj.group(1), mobj.group(2)))
    
    SIM = 0
    EQ = 1
    # --------------------------------------------------
    # Load tables
    # --------------------------------------------------
    def load_table(csv_path):
        with open(csv_path, newline='', encoding=encoding) as f:
            reader = csv.DictReader(f)
            rows = list(reader)
            headers = reader.fieldnames
        return rows, headers

    table1, headers1 = load_table(table1_csv)
    table2, headers2 = load_table(table2_csv)

    # --------------------------------------------------
    # Entity attributes
    # --------------------------------------------------
    ent_attr1, ent_attr2 = entity_attrs

    left_vals = {
        row[ent_attr1]
        for row in table1
        if not utils.is_empty(row.get(ent_attr1))
    }

    right_vals = {
        row[ent_attr2]
        for row in table2
        if not utils.is_empty(row.get(ent_attr2))
    }

    # --------------------------------------------------
    # Default attribute pairs
    # --------------------------------------------------
    if attr_pairs is None:
        skip = {"tid", "id"}
        common_attrs = (set(headers1) & set(headers2)) - skip
        attr_pairs = [(a, a, 1.0) for a in common_attrs]

    attrs, weights = zip(*[((a1, a2), w) for a1, a2, w in attr_pairs])

    # --------------------------------------------------
    # Build value → records index
    # --------------------------------------------------
    def build_index(table):
        index = defaultdict(list)
        for row in table:
            for v in row.values():
                index[v].append(row)
        return index

    index1 = build_index(table1)
    index2 = build_index(table2)

    # --------------------------------------------------
    # Candidate negatives from entity attributes
    # --------------------------------------------------
    candidates = [
        (v1, v2)
        for v1 in left_vals
        for v2 in right_vals
        if (v1, v2) not in positives
    ]

    random.shuffle(candidates)
    sampled_cnt_dict = {(a1,a2):0  for (a1,a2) in attrs}
    length_dict = {(a1,a2):int(w*size) for a1, a2, w in attr_pairs}
    # --------------------------------------------------
    # Sampling loop
    # --------------------------------------------------
    results = set()
    attrs = list(attrs)
    weights = list(weights)
    # {print(v) for _,v in sampled_cnt_dict.items()}
    # while any(v == 0 for _,v in sampled_cnt_dict.items()):
    for v1, v2 in candidates:
        #print(sampled_cnt_dict)
        if len(results) >= size:
            break
        for attp in attrs:
            if sampled_cnt_dict[attp] >= length_dict[attp]:
                idx = attrs.index(attp)
                attrs.remove(attp)
                weights.pop(idx)
        recs1 = index1.get(v1)
        #print('11111',recs1)
        recs2 = index2.get(v2)
        #print('22222',recs2)

        if not recs1 or not recs2:
            continue

        r1 = random.choice(recs1)
        r2 = random.choice(recs2)

        # chosen_attrs = random.choices(attrs, weights=weights, k=m)
        picked = False
        for i, (a1,a2) in enumerate(attrs):
            if picked:
                break
            # passed = True
            val1 = r1.get(a1)
            val2 = r2.get(a2)

            if utils.is_empty(val1) or utils.is_empty(val2):
                #passed = False
                continue
            sim_pair_thresh = [(_a1,_a2,theta) for _a1,_a2,theta in sim_defined if a1 == _a1 and a2 == _a2]
            if random.random() >= 0.8 and len(sim_pair_thresh)>0:
                theta = sim_pair_thresh[0][2]
                if not sim(val1, val2, theta):
                    #passed = False
                    continue

                sampled_cnt_dict[(a1,a2)]+=1
                picked = True
                print(a1,a2, f'sim sampled {v1},{v2}')

            else:
                if val1 != val2:
                    #passed = False
                    continue
                sampled_cnt_dict[(a1,a2)]+=1
                picked = True
                print(a1,a2, f'eq sampled {v1},{v2}')
        if picked :
            results.add(f'neg(eqo("{v1}","{v2}")).')        

    return results

def sample_negative_examples_multi(
    positive_pairs: Set[str],
    table1_csv: str,
    table2_csv: str,
    related_csvs: List[Tuple[str, str]],   # [(join_attr, related_csv_path)]
    entity_attrs: Tuple[str, str],
    attr_pairs: List[Tuple[str, str, float]] | None,
    size: int,
    m: int,
    sim: Callable[[str, str, float], bool],
    encoding='utf-8',
    sim_defined: Set[tuple] = None,
    to_skip = set()
) -> Set[str]:
    """
    Negative sampling using:
      1. attribute pairs from the main table
      2. attribute pairs from related tables joined through entity ids

    Assumes table1_csv == table2_csv (same table/entity set).
    """

    import csv
    import re
    import random
    from collections import defaultdict

    # --------------------------------------------------
    # Parse positive ASP facts
    # --------------------------------------------------
    pattern = re.compile(r'pos\(eqo\("(.+?)","(.+?)"\)\)\.')

    positives = set()
    for s in positive_pairs:
        mobj = pattern.match(s.strip())
        if mobj:
            positives.add((mobj.group(1), mobj.group(2)))
            positives.add((mobj.group(2), mobj.group(1)))

    # --------------------------------------------------
    # Load tables
    # --------------------------------------------------
    def load_table(csv_path):
        with open(csv_path, newline='', encoding=encoding) as f:
            reader = csv.DictReader(f)
            rows = list(reader)
            headers = reader.fieldnames
        return rows, headers

    table1, headers1 = load_table(table1_csv)
    table2, headers2 = load_table(table2_csv)

    # related_csvs = [(join_attr, csv_path)]
    related_tables = []
    for join_attr, path in related_csvs:
        rows, headers = load_table(path)
        related_tables.append((join_attr, rows, headers))

    # --------------------------------------------------
    # Entity attributes
    # --------------------------------------------------
    ent_attr1, ent_attr2 = entity_attrs

    left_vals = {
        row[ent_attr1]
        for row in table1
        if not utils.is_empty(row.get(ent_attr1))
    }

    right_vals = {
        row[ent_attr2]
        for row in table2
        if not utils.is_empty(row.get(ent_attr2))
    }

    # --------------------------------------------------
    # Default attribute pairs
    # --------------------------------------------------
    if attr_pairs is None:

        attr_pairs = []
        
        skip = {"tid", ent_attr1}

        # main table attributes
        common_attrs = (set(headers1) & set(headers2)) - skip - to_skip

        for a in common_attrs:
            attr_pairs.append((a, a, 1.0))
        
        # related table attributes
        for join_attr, _, headers in related_tables:
            for h in headers:
                if h in skip or h == join_attr or h in to_skip:
                    continue
                attr_pairs.append((h, h, 1.0))
        
        weight = 1/len(attr_pairs)
        
    attrs, weights = zip(*[((a1, a2), weight) for a1, a2, _ in attr_pairs])
    # print(attr_pairs, attrs, weights)
    # --------------------------------------------------
    # Build main-table entity index
    # --------------------------------------------------
    def build_entity_index(table, ent_attr):
        index = {}
        for row in table:
            val = row.get(ent_attr)
            if not utils.is_empty(val):
                index[val] = row
        return index

    entity_index1 = build_entity_index(table1, ent_attr1)
    entity_index2 = build_entity_index(table2, ent_attr2)

    # --------------------------------------------------
    # Build related-table join index
    # --------------------------------------------------
    # related_indexes[join_attr][entity_id] -> list(rows)
    # --------------------------------------------------
    related_indexes = {}

    for join_attr, rows, headers in related_tables:

        idx = defaultdict(list)

        for row in rows:
            key = row.get(join_attr)

            if utils.is_empty(key):
                continue

            idx[key].append(row)

        related_indexes[join_attr] = idx

    # --------------------------------------------------
    # Candidate negatives
    # --------------------------------------------------
    candidates = [
        (v1, v2)
        for v1 in left_vals
        for v2 in right_vals
        if v1 != v2 and (v1, v2) not in positives
    ]

    random.shuffle(candidates)

    sampled_cnt_dict = {(a1, a2): 0 for (a1, a2) in attrs}
    length_dict = {(a1, a2): int(weight * size) for a1, a2, _ in attr_pairs}
    print(length_dict)
    # --------------------------------------------------
    # Helper: collect attribute values
    # --------------------------------------------------
    def collect_values(entity_id, entity_row, attr_name, side=1):

        vals = []

        # main table value
        if attr_name in entity_row:
            v = entity_row.get(attr_name)
            if not utils.is_empty(v):
                vals.append(v)

        # related table values
        for join_attr, rows, headers in related_tables:

            if attr_name not in headers:
                continue

            related_rows = related_indexes[join_attr].get(entity_id, [])

            for rr in related_rows:
                v = rr.get(attr_name)

                if not utils.is_empty(v):
                    vals.append(v)

        return vals

    # --------------------------------------------------
    # Sampling loop
    # --------------------------------------------------
    results = set()

    attrs = list(attrs)
    weights = list(weights)

    for v1, v2 in candidates:

        if len(results) >= size:
            break

        # remove saturated attributes
        for attp in list(attrs):

            if sampled_cnt_dict[attp] >= length_dict[attp]:

                idx = attrs.index(attp)

                attrs.remove(attp)
                weights.pop(idx)

        if len(attrs) == 0:
            break

        r1 = entity_index1.get(v1)
        r2 = entity_index2.get(v2)

        if not r1 or not r2:
            continue

        picked = False

        for (a1, a2) in attrs:

            if picked:
                break

            vals1 = collect_values(v1, r1, a1, side=1)
            vals2 = collect_values(v2, r2, a2, side=2)

            if len(vals1) == 0 or len(vals2) == 0:
                continue

            sim_pair_thresh = [
                (_a1, _a2, theta)
                for _a1, _a2, theta in sim_defined
                if a1 == _a1 and a2 == _a2
            ] if sim_defined else []

            matched = False

            # --------------------------------------------------
            # compare ALL combinations
            # --------------------------------------------------
            for val1 in vals1:

                if matched:
                    break

                for val2 in vals2:

                    if utils.is_empty(val1) or utils.is_empty(val2):
                        continue

                    # similarity sampling
                    if random.random() >= 0.8 and len(sim_pair_thresh) > 0:

                        theta = sim_pair_thresh[0][2]

                        if sim(val1, val2, theta):

                            matched = True
                            print(a1, a2, f'sim sampled {v1},{v2}')
                            break

                    # equality sampling
                    else:

                        if val1 == val2:

                            matched = True
                            print(a1, a2, f'eq sampled {v1},{v2}')
                            break

            if matched:

                sampled_cnt_dict[(a1, a2)] += 1
                picked = True

        if picked:
            results.add(f'neg(eqo("{v1}","{v2}")).')

    return results

def sample_negative_examples5(
    positive_pairs: Set[str],
    table1_csv: str,
    table2_csv: str,
    entity_attrs: Tuple[str, str],   # <-- NEW
    attr_pairs: List[Tuple[str, str, float]] | None,
    size: int,
    m: int,
    sim: Callable[[str, str], bool],
    encoding='utf-8',
    sim_defined : Set[tuple]  = None,
) -> Set[str]:
    """
    Negative pairs are generated by recombining entity values taken
    from specified attributes of the two tables.
    """

    # --------------------------------------------------
    # Parse positive ASP facts
    # --------------------------------------------------
    pattern = re.compile(r'pos\(eqo\("(.+?)","(.+?)"\)\)\.')

    positives = set()
    for s in positive_pairs:
        mobj = pattern.match(s.strip())
        if mobj:
            positives.add((mobj.group(1), mobj.group(2)))
    
    SIM = 0
    EQ = 1
    # --------------------------------------------------
    # Load tables
    # --------------------------------------------------
    def load_table(csv_path):
        with open(csv_path, newline='', encoding=encoding) as f:
            reader = csv.DictReader(f)
            rows = list(reader)
            headers = reader.fieldnames
        return rows, headers

    table1, headers1 = load_table(table1_csv)
    table2, headers2 = load_table(table2_csv)

    # --------------------------------------------------
    # Entity attributes
    # --------------------------------------------------
    ent_attr1, ent_attr2 = entity_attrs

    left_vals = {
        row[ent_attr1]
        for row in table1
        if not utils.is_empty(row.get(ent_attr1))
    }

    right_vals = {
        row[ent_attr2]
        for row in table2
        if not utils.is_empty(row.get(ent_attr2))
    }

    # --------------------------------------------------
    # Default attribute pairs
    # --------------------------------------------------
    if attr_pairs is None:
        skip = {"tid", "id"}
        common_attrs = (set(headers1) & set(headers2)) - skip
        attr_pairs = [(a, a, 1.0) for a in common_attrs]

    attrs, weights = zip(*[((a1, a2), w) for a1, a2, w in attr_pairs])

    # --------------------------------------------------
    # Build value → records index
    # --------------------------------------------------
    def build_index(table):
        index = defaultdict(list)
        for row in table:
            for v in row.values():
                index[v].append(row)
        return index

    index1 = build_index(table1)
    index2 = build_index(table2)

    # --------------------------------------------------
    # Candidate negatives from entity attributes
    # --------------------------------------------------
    candidates = [
        (v1, v2)
        for v1 in left_vals
        for v2 in right_vals
        if (v1, v2) not in positives
    ]

    random.shuffle(candidates)
    sampled_cnt_dict = {(a1,a2):0  for (a1,a2) in attrs}
    length_dict = {(a1,a2):int(w*size) for a1, a2, w in attr_pairs}
    # --------------------------------------------------
    # Sampling loop
    # --------------------------------------------------
    results = set()
    attrs = list(attrs)
    weights = list(weights)
    # {print(v) for _,v in sampled_cnt_dict.items()}
    # while any(v == 0 for _,v in sampled_cnt_dict.items()):
    for v1, v2 in candidates:
        #print(sampled_cnt_dict)
        if len(results) >= size:
            break
        for attp in attrs:
            if sampled_cnt_dict[attp] >= length_dict[attp]:
                idx = attrs.index(attp)
                attrs.remove(attp)
                weights.pop(idx)
        recs1 = index1.get(v1)
        #print('11111',recs1)
        recs2 = index2.get(v2)
        #print('22222',recs2)

        if not recs1 or not recs2:
            continue

        r1 = random.choice(recs1)
        r2 = random.choice(recs2)

        # chosen_attrs = random.choices(attrs, weights=weights, k=m)
        picked = False
        for i, (a1,a2) in enumerate(attrs):
            if picked:
                break
            # passed = True
            val1 = r1.get(a1)
            val2 = r2.get(a2)

            if utils.is_empty(val1) or utils.is_empty(val2):
                #passed = False
                continue
            sim_pair_thresh = [(_a1,_a2,theta) for _a1,_a2,theta in sim_defined if a1 == _a1 and a2 == _a2]
            if random.random() >= 0.8 and len(sim_pair_thresh)>0:
                theta = sim_pair_thresh[0][2]
                if not sim(val1, val2, theta):
                    #passed = False
                    continue

                sampled_cnt_dict[(a1,a2)]+=1
                picked = True
                print(a1,a2, f'sim sampled {v1},{v2}')

            else:
                if val1 != val2:
                    #passed = False
                    continue
                sampled_cnt_dict[(a1,a2)]+=1
                picked = True
                print(a1,a2, f'eq sampled {v1},{v2}')
        if picked :
            results.add(f'neg(eqo("{v1}","{v2}")).')        

    return results

def sample_negative_examples2(
    all_neg_pairs_csv: str,
    table1_csv: str,
    table2_csv: str,
    attr_pairs: List[Tuple[str, str, float]] | None,
    size: int,
    m: int,
    sim: Callable[[str, str], bool],
    encoding = 'utf-8',
    sim_defined: Set[tuple] = None,
) -> Set[str]:
    """
    Synthesise negative examples under attribute-level constraints.

    Returns:
        A set of ASP facts of the form:
        neg(eqo("v1","v2")).
    """

    # --------------------------------------------------
    # Load tables indexed by attribute values
    # --------------------------------------------------
    def load_table(csv_path):
        with open(csv_path, newline='', encoding=encoding) as f:
            reader = csv.DictReader(f)
            rows = list(reader)
            headers = reader.fieldnames
        return rows, headers

    table1, headers1 = load_table(table1_csv)
    table2, headers2 = load_table(table2_csv)

    # --------------------------------------------------
    # Default attribute pairs (same-name attrs, weight=1)
    # --------------------------------------------------
    if attr_pairs is None:
        skip = {"tid", "id"}
        common_attrs = (set(headers1) & set(headers2)) - skip
        attr_pairs = [(a, a, 1.0) for a in common_attrs]

    attrs, weights = zip(*[((a1, a2), w) for a1, a2, w in attr_pairs])

    # --------------------------------------------------
    # Build value → records index
    # --------------------------------------------------
    def build_index(table):
        index = defaultdict(list)
        for row in table:
            for v in row.values():
                index[v].append(row)
        return index

    index1 = build_index(table1)
    index2 = build_index(table2)

    # --------------------------------------------------
    # Load candidate negative pairs
    # --------------------------------------------------
    with open(all_neg_pairs_csv, newline='', encoding=encoding) as f:
        reader = csv.reader(f)
        next(reader)  # header
        candidates = [(v1, v2) for v1, v2 in reader]

    random.shuffle(candidates)

    # --------------------------------------------------
    # Sampling loop
    # --------------------------------------------------
    results = set()

    for v1, v2 in candidates:
        if len(results) >= size:
            break

        recs1 = index1.get(v1)
        recs2 = index2.get(v2)

        if not recs1 or not recs2:
            continue

        r1 = random.choice(recs1)
        r2 = random.choice(recs2)

        # weighted sampling of attribute pairs
        chosen_attrs = random.choices(attrs, weights=weights, k=m)

        passed = True
        for a1, a2 in chosen_attrs:
            val1 = r1.get(a1)
            val2 = r2.get(a2)

            if utils.is_empty(val1)  or utils.is_empty(val2) is None:
                passed = False
                break

            # balance equality vs similarity
            if random.random() >= 0.7 and (a1,a2) in sim_defined:
                if not sim(val1, val2):
                    passed = False
                    break
            else:
                if val1 != val2:
                    passed = False
                    break
                # else:
                #     print(v1,v2,a1,a2)

                # else:
                #     print(v1,v2,a1,a2)

        if passed:
            results.add(f'neg(eqo("{v1}","{v2}")).')

    return results




def _tokenize_record(row, exclude_cols):
    values = [
        str(v).lower().strip()
        for col, v in row.items()
        if col not in exclude_cols and pd.notna(v)
    ]
    text = " ".join(values)
    tokens = re.findall(r"\w+", text)
    return set(tokens)


def _jaccard(a, b):
    if not a and not b:
        return 0.0
    return len(a & b) / len(a | b)


def sample_negative_pairs3(
    table1_csv: str,
    table2_csv: str,
    sample_size: int,
    exclude_attributes: Set[str],
    all_negative_pairs_csv: str,
    similarity_threshold: float,
) -> Set[str]:
    """
    Returns:
        set of strings:
        neg(eqo("v1","v2")).
    """

    # load tables
    df1 = pd.read_csv(table1_csv)
    df2 = pd.read_csv(table2_csv)

    # load all candidate negative pairs
    # expected columns: id1,id2
    neg_pairs_df = pd.read_csv(all_negative_pairs_csv)

    # pre-tokenize records
    tokens1 = {
        idx: _tokenize_record(row, exclude_attributes)
        for idx, row in df1.iterrows()
    }

    tokens2 = {
        idx: _tokenize_record(row, exclude_attributes)
        for idx, row in df2.iterrows()
    }

    # shuffle candidates
    candidates = list(neg_pairs_df.itertuples(index=False))
    random.shuffle(candidates)

    sampled = set()

    for row in candidates:
        if len(sampled) >= sample_size:
            break

        i = row[0]
        j = row[1]

        if i not in tokens1 or j not in tokens2:
            continue

        sim = _jaccard(tokens1[i], tokens2[j])

        if sim >= similarity_threshold:
            sampled.add(f'neg(eqo("{i}","{j}")).')

    return sampled

def _string_sim(a, b):
    if pd.isna(a) or pd.isna(b):
        return 0.0

    a = str(a).lower().strip()
    b = str(b).lower().strip()

    return max(
        fuzz.token_sort_ratio(a, b),
        fuzz.token_set_ratio(a, b),
        fuzz.partial_ratio(a, b),
    )


def _record_similarity(r1, r2, exclude):
    sims = []

    for col in r1.index:
        if col in exclude:
            continue

        sims.append(_string_sim(r1[col], r2[col]))

    if not sims:
        return 0.0

    return sum(sims) / len(sims)


def sample_negative_pairs4(
    table1_csv: str,
    table2_csv: str,
    sample_size: int,
    exclude_attributes: Set[str],
    all_negative_pairs_csv: str,
    similarity_threshold: float,
    encoding="utf-8",
    id_column = 0
):

    df1 = pd.read_csv(table1_csv, encoding=encoding)
    df2 = pd.read_csv(table2_csv, encoding=encoding)

    neg_pairs = pd.read_csv(all_negative_pairs_csv, encoding=encoding)

    # assume first column is value used in eqo(...)
    key1 = df1.columns[id_column]
    key2 = df2.columns[id_column]

    # build lookup by value
    map1 = {str(row[key1]): row for _, row in df1.iterrows()}
    map2 = {str(row[key2]): row for _, row in df2.iterrows()}

    candidates = list(neg_pairs.itertuples(index=False))
    random.shuffle(candidates)

    sampled = set()

    for v1, v2 in candidates:

        if len(sampled) >= sample_size:
            break

        v1 = str(v1)
        v2 = str(v2)

        if v1 not in map1 or v2 not in map2:
            continue

        sim = _record_similarity(map1[v1], map2[v2], exclude_attributes)
        if sim >= similarity_threshold:
            
            sampled.add(f'neg(eqo("{v1}","{v2}")).')

    return sampled

def sample_negative_pairs5(
    table1_csv: str,
    table2_csv: str,
    sample_size: int,
    exclude_attributes: Set[str],
    positive_facts: Set[str],
    similarity_threshold: float,
    encoding="utf-8",
):

    df1 = pd.read_csv(table1_csv, encoding=encoding)
    df2 = pd.read_csv(table2_csv, encoding=encoding)

    # assume first column is value used in eqo(...)
    key1 = df1.columns[0]
    key2 = df2.columns[0]

    map1 = {str(row[key1]): row for _, row in df1.iterrows()}
    map2 = {str(row[key2]): row for _, row in df2.iterrows()}

    # ----------------------------
    # extract positives
    # ----------------------------
    pattern = r'pos\(eqo\("(.+?)","(.+?)"\)\)\.'

    pos_pairs = set()
    left_vals = set()
    right_vals = set()

    for fact in positive_facts:
        m = re.match(pattern, fact.strip())
        if not m:
            continue

        v1, v2 = m.group(1), m.group(2)

        pos_pairs.add((v1, v2))
        left_vals.add(v1)
        right_vals.add(v2)

    # ----------------------------
    # generate candidate negatives
    # ----------------------------
    candidates = set()

    for v1 in left_vals:
        for v2 in right_vals:
            if (v1, v2) not in pos_pairs:
                candidates.add((v1, v2))

    candidates = list(candidates)
    random.shuffle(candidates)

    # ----------------------------
    # similarity filtering
    # ----------------------------
    sampled = set()

    for v1, v2 in candidates:

        if len(sampled) >= sample_size:
            break

        if v1 not in map1 or v2 not in map2:
            continue

        sim = _record_similarity(map1[v1], map2[v2], exclude_attributes)

        if sim >= similarity_threshold:
            sampled.add(f'neg(eqo("{v1}","{v2}")).')

    return sampled

def dblp_atoms():
    dblp_data = dataloader.Dataloader(path_list=['../data/dblp/dblp.csv','../data/dblp/acm.csv'],ground_truth=['../data/dblp/dblp-id_acm-id.csv'],encoding=dataloader.ISO)
    tbls = dblp_data.load_data()
    dblp_schema = Schema('dblp','dblp',tbls=tbls, spec_dir=f'./lp/dblp-trc/dblp-schema.lp', is_trc=False,ver=LACE_P)
    dblp_path = '../data/dblp/dblp.csv'
    acm_path = '../data/dblp/acm.csv'
    # dblp_acm = load_atombase_trc(dblp_schema)
    atoms = csv_to_asp_facts('../data/dblp/dblp.csv',encoding='ISO-8859-1',attr_prefix='d')
    atoms2 = csv_to_asp_facts('../data/dblp/acm.csv',encoding='ISO-8859-1',attr_prefix='a')
    atoms+= atoms2
    # print(csv_to_asp_facts('../data/dblp/dblp.csv'))
    
    
    sim_pairs = {('dblp',2,'acm',2):90, ('dblp',3,'acm',3):90, ('dblp',4,'acm',4):90, ('dblp',5,'acm',5):90}
    sims = get_naive_sim(dblp_schema,sim_pairs )
    atoms = set(atoms).union(sims)
    print('\n'.join(atoms))
    
def dblp_scholar_atoms():
    dblp_path = '../data/dblp-scholar/dblp.csv'
    scholars_path = '../data/dblp-scholar/scholar.csv'
    dblp_data = dataloader.Dataloader(path_list=[dblp_path,scholars_path],ground_truth=['../data/dblp-scholar/DBLP-Scholar_perfectMapping.csv'],encoding='latin1')
    tbls = dblp_data.load_data()
    dblp_schema = Schema('dblp','dblp',tbls=tbls, spec_dir=f'./lp/dblp-scholar/dblp-schema.lp', is_trc=False,ver=LACE_P)

    # dblp_acm = load_atombase_trc(dblp_schema)
    atoms = csv_to_asp_facts(dblp_path,encoding='latin1',attr_prefix='d')
    atoms2 = csv_to_asp_facts(scholars_path,encoding='latin1',attr_prefix='s')
    atoms+= atoms2
    # print(csv_to_asp_facts('../data/dblp/dblp.csv'))
    
    sim_pairs = {('dblp',2,'scholar',2):90, ('dblp',3,'scholar',3):90, ('dblp',4,'scholar',4):90}
    sims = get_naive_sim(dblp_schema,sim_pairs,True)
    atoms = set(atoms).union(sims)
    print('\n'.join(sims))
    
    
def amazon_google_atoms():
    amaz_path = '../data/amazon-google/amazon.csv'
    google_path = '../data/amazon-google/google.csv'
    dblp_data = dataloader.Dataloader(path_list=[amaz_path,google_path],ground_truth=['../data/dblp-scholar/Amzon_GoogleProducts_perfectMapping.csv'],encoding='latin1')
    tbls = dblp_data.load_data()
    dblp_schema = Schema('amazon-google','amz_gl',tbls=tbls, spec_dir=f'./lp/amazon-google/am-gl-schema.lp', is_trc=False,ver=LACE_P)

    # dblp_acm = load_atombase_trc(dblp_schema)
    atoms = csv_to_asp_facts(amaz_path,encoding='latin1',attr_prefix='a')
    atoms2 = csv_to_asp_facts(google_path,encoding='latin1',attr_prefix='g')
    atoms+= atoms2
    # print(csv_to_asp_facts('../data/dblp/dblp.csv'))
    
    sim_pairs = {('amazon',2,'google',2):90, ('amazon',3,'google',3):90, ('amazon',4,'google',4):90,('amazon',5,'google',5):90}
    sims = get_naive_sim(dblp_schema,sim_pairs,True)
    atoms = set(atoms).union(sims)
    print('\n'.join(atoms))    


def pokemon_species_atoms():
    SPECIES = f'species' 
    SPECIES_NAME = f'spec_name'
    SPECIES_DESC = f'spec_desc'
    MOVE = f'move' 
    MOVE_NAME = f'move_name'
    MOVE_DESC = f'move_desc'
    POKE_PATH = f'../data/pokemon/'
    #sim_attrs = get_reduced_spec(file)[1]
    path_list = [POKE_PATH+f'/{SPECIES}.csv',POKE_PATH+f'/{SPECIES_NAME}.csv',POKE_PATH+f'/{SPECIES_DESC}.csv']
    dblp_data = dataloader.Dataloader(path_list=path_list,ground_truth=[f'{POKE_PATH}/{SPECIES}_dup.csv'])
    tbls = dblp_data.load_data()
    dblp_schema = Schema('imdb','imdb',tbls=tbls, spec_dir=f'./lp/amazon-google/am-gl-schema.lp', is_trc=False,ver=LACE_P)
    # dblp_acm = load_atombase_trc(dblp_schema)
    atoms = []
    for p in path_list:
        atoms += csv_to_asp_facts(p)
    # print(csv_to_asp_facts('../data/dblp/dblp.csv'))
    sim_pairs = {(f'{SPECIES_NAME}',3,f'{SPECIES_NAME}',3):90, (f'{SPECIES_NAME}',4,f'{SPECIES_NAME}',4):90, (f'{SPECIES_DESC}',4,f'{SPECIES_DESC}',4):85}
    sims = get_naive_sim(dblp_schema,sim_pairs )
    atoms = set(atoms).union(sims)
    print('\n'.join(sims))    
    
    
    
# def pokemon_schema(split='',files=[],ver=LACE)->tuple[Schema,Dataloader]:
#     TEST = '' if len(split) == 0 else '_'+split
#     # A = ')'
#     # A = ''
#     # 0 out degree
#     # ability -> species -> items -> moves
#     # ability -> 
#     # generation variants
#     # main_series variants
#     file = files[0]
#     #sim_attrs = get_reduced_spec(file)[1]
#     POKEMON = f'pokemon' 
#     SPECIES = f'species' 
#     SPECIES_NAME = f'spec_name'
#     SPECIES_DESC = f'spec_desc'
#     POKEMON_ITEM = f'poke_item' 
#     POKEMON_MOVE = f'poke_move' 
#     POKEMON_STATS = f'poke_stats'
#     POKEMON_TYPE = f'poke_type'
#     ITEM = f'item' 
#     ITEM_NAME = f'item_name'
#     ITEM_DESC = f'item_desc'
#     # MACHINE = f'machine'
#     ABILITY = f'ability' 
#     ABILITY_NAME = f'ability_name'
#     ABILITY_DESC = f'ability_desc'
#     POKEMON_ABILITY = f'poke_ability' 
#     MOVE = f'move' 
#     MOVE_NAME = f'move_name'
#     MOVE_DESC = f'move_desc'
#     STATS = f'stats'
#     TYPE = f'type'
    
#     name_list = [ POKEMON ,
#     SPECIES ,
#     SPECIES_NAME,
#     SPECIES_DESC,
#     POKEMON_ITEM ,
#     POKEMON_MOVE,
#     POKEMON_STATS ,
#     POKEMON_TYPE,
#     ITEM ,
#     ITEM_NAME ,
#     ITEM_DESC,
#     # MACHINE ,
#     ABILITY,
#     ABILITY_NAME,
#     ABILITY_DESC,
#     POKEMON_ABILITY,
#     MOVE,
#     MOVE_NAME,
#     MOVE_DESC,
#     STATS,
#     TYPE]
#     # T_RATINGS = f'title_ratings{TEST}' 
#     ref_dict =    {
#      (SPECIES,'evolves_from_species'):(SPECIES,'species'), # self join
#      (POKEMON,'species'):(SPECIES,'species'),
#      (SPECIES_NAME,'species'):(SPECIES,'species'),
#      (SPECIES_DESC,'species'):(SPECIES,'species'),
#      (POKEMON_ITEM,'pokemon'):(POKEMON,'pokemon'),
#      (POKEMON_ITEM,'item'):(ITEM,'item'),
#      (ITEM_NAME,'item'):(ITEM,'item'),
#      (ITEM_DESC,'item'):(ITEM,'item'),
#      (POKEMON_MOVE,'move'):(MOVE,'move'),
#      (POKEMON_MOVE,'pokemon'):(POKEMON,'pokemon'),
#      (MOVE_NAME,'move'):(MOVE,'move'),
#      (MOVE_DESC,'move'):(MOVE,'move'),
#      (POKEMON_ABILITY,'pokemon'):(POKEMON,'pokemon'),
#      (POKEMON_ABILITY,'ability'):(ABILITY,'ability'),
#      (ABILITY_NAME,'ability'):(ABILITY,'ability'),
#      (ABILITY_DESC,'ability'):(ABILITY,'ability'),
#      # (MACHINE,'item'):(ITEM,'item'),
#      # (MACHINE,'move'):(MOVE,'move'),
#      (POKEMON_TYPE,'pokemon'):(POKEMON,'pokemon'),
#      (POKEMON_TYPE,'type'):(TYPE,'type'),
#      (POKEMON_STATS,'pokemon'):(POKEMON,'pokemon'),
#      (POKEMON_STATS,'stats'):(STATS,'stats'),
#      }
#     # MUSIC_PATH = '/scratch/c.c2028447/project/entity-resolution/dataset/musicbrainz'
#     POKEMON_PATH = f'./dataset/pokemon/{split}'
#     dup_rel = {POKEMON,SPECIES,ITEM,ABILITY,MOVE}
#     path_list = [POKEMON_PATH + f'/{name}.csv' for name in name_list]
#     ground_truth_list = [POKEMON_PATH + f'/{name}_dups.csv' for name in dup_rel]
    
#     dl_poke = Dataloader(name = f'pokemon_{split}',path_list=path_list,ground_truth=ground_truth_list)
#     tbls = dl_poke.load_data()  
#     tbls_dict = {t[0]:(0,t[1]) for t in tbls}
#     del tbls 
#     dtype_cfg = POKEMON_PATH+f'/domain.yml'
#     order = name_list
#     pokemon = Schema(id = '3',name =f'pokemon{TEST}',tbls=tbls_dict,refs=ref_dict,dup_rels=dup_rel,attr_types=utils.load_config(dtype_cfg),order=order,spec_dir=file,ver=ver)
#     #pokemon.set_sim_attrs(sim_attrs)
#     return pokemon,dl_poke
    
    
def imdb_atoms():
    T_BASIC = f'title_basics' 
    N_BASIC = f'name_basics' 
    T_AKA = f'title_akas' 
    T_PRINCIPLE = f'title_principals' 
    T_RATINGS = f'title_ratings' 
    IMDB_PATH = f'../data/imdb/'
    #sim_attrs = get_reduced_spec(file)[1]
    path_list = [IMDB_PATH+f'/title_akas.csv',IMDB_PATH+f'/name_basics.csv',IMDB_PATH+f'/title_basics.csv',IMDB_PATH+f'/title_principals.csv',IMDB_PATH+f'/title_ratings.csv']
    dblp_data = dataloader.Dataloader(path_list=path_list,ground_truth=[f'{IMDB_PATH}/{N_BASIC}_dup.csv', f'{IMDB_PATH}/{T_BASIC}_dup.csv'])
    tbls = dblp_data.load_data()
    dblp_schema = Schema('imdb','imdb',tbls=tbls, spec_dir=f'./lp/amazon-google/am-gl-schema.lp', is_trc=False,ver=LACE_P)
    # dblp_acm = load_atombase_trc(dblp_schema)
    atoms = []
    # for p in path_list:
    #     atoms += csv_to_asp_facts(p)
    # print(csv_to_asp_facts('../data/dblp/dblp.csv'))
    sim_pairs = {('title_basics',2,'title_basics',2):90, ('title_basics',3,'title_basics',3):85, ('title_basics',4,'title_basics',4):85, 
    ('title_basics',7,'title_basics',7):90, # ('name_basics',2,'name_basics',2):90, 
     # ('name_basics',3,'name_basics',3):90, 
     (T_AKA,3,T_AKA,3):85}
    sims = get_naive_sim(dblp_schema,sim_pairs, with_thresh=True)
    atoms = set(atoms).union(sims)
    print('\n'.join(sims))    
    
    


def cora_atoms():
    dblp_data = dataloader.Dataloader(path_list=['../data/cora/cora.csv'],ground_truth=['../data/cora/cora_DPL.csv'])
    tbls = dblp_data.load_data()
    cora = Schema('cora','cora',tbls=tbls, spec_dir=f'./lp/cora/cora-schema.lp', is_trc=False,ver=LACE_P)
    cora_path = '../data/cora/cora.csv'
    acm_path = '../data/dblp/acm.csv'
    # dblp_acm = load_atombase_trc(dblp_schema)
    atoms = csv_to_asp_facts(cora_path,encoding='ISO-8859-1')
    # atoms2 = csv_to_asp_facts('../data/dblp/acm.csv',encoding='ISO-8859-1',attr_prefix='a')
    # atoms+= atoms2
    # print(csv_to_asp_facts('../data/dblp/dblp.csv'))
    sim_defined = {('address','address',90), ('authors','authors',85), ('booktitle','booktitle',90), ('date','date',95),('editor','editor',90)
                   ,('institution','institution',90),('journal','journal',90), ('note','note',85),('pages','pages',95), ('publisher','publisher',90),
                   ('title','title',90),('type','type',90),('volume','volume',95),('year','year',95)}
    
    sim_pairs = {('cora',1, 'cora',1):90, ('cora',2,'cora',2):85, ('cora',3,'cora',3):90, 
                 ('cora',4,'cora',4):95, ('cora',5,'cora',5):90, ('cora',7,'cora',7):90, 
                 ('cora',8,'cora',8):90, ('cora',10,'cora',10):85, 
                 ('cora',11,'cora',11):95, ('cora',12,'cora',12):90, 
                 ('cora',14,'cora',14):90,('cora',15,'cora',15):90, ('cora',16,'cora',16):95, 
                 ('cora',17,'cora',17):95}

    sims = get_naive_sim(cora,sim_pairs,with_thresh=True)
    atoms = set(atoms).union(sims)
    print('\n'.join(sims))
    
    
def cddb_atoms():
    dblp_data = dataloader.Dataloader(path_list=['../data/cddb/cddb.csv'],ground_truth=['../data/cddb/cddb_DPL.csv'])
    tbls = dblp_data.load_data()
    cora = Schema('cddb','cddb',tbls=tbls, spec_dir=f'./lp/cora/cora-schema.lp', is_trc=False,ver=LACE_P)
    cora_path = '../data/cddb/cddb.csv'
    acm_path = '../data/dblp/acm.csv'
    # dblp_acm = load_atombase_trc(dblp_schema)
    atoms = csv_to_asp_facts(cora_path,encoding='ISO-8859-1')
    # atoms2 = csv_to_asp_facts('../data/dblp/acm.csv',encoding='ISO-8859-1',attr_prefix='a')
    # atoms+= atoms2
    # print(csv_to_asp_facts('../data/dblp/dblp.csv'))
    sim_defined = {('artist','artist',90), ('category','category',90), ('genre','genre',90),('title','title',90),('track','track',85)}

    sim_pairs = {('cddb',1, 'cddb',1):90, ('cddb',2,'cddb',2):90, ('cddb',3,'cddb',3):90, 
                ('cddb',5,'cddb',5):90, ('cddb',6,'cddb',6):85}

    sims = get_naive_sim(cora,sim_pairs,with_thresh=True)
    atoms = set(atoms).union(sims)
    print('\n'.join(sims))
    
def dblp_neg_generation():
    ground_truth='../data/dblp/dblp-id_acm-id.csv'
    dblp_path = '../data/dblp/dblp.csv'
    acm_path = '../data/dblp/acm.csv'
    pair= ('id','id')
    generate_non_gt_pairs(gt_csv_path=ground_truth, table1_csv_path=dblp_path, table2_csv_path=acm_path, attr_pair= pair,output_csv_path='../data/dblp/neg-all.csv',encoding='ISO-8859-1')

def dblp_scholar_neg_generation(base_dir = '../data/dblp-scholar'):
    ground_truth=f'{base_dir}/DBLP-Scholar_perfectMapping.csv'
    dblp_path = f'{base_dir}/dblp.csv'
    acm_path = f'{base_dir}/scholar.csv'
    pair= ('id','id')
    generate_non_gt_pairs(gt_csv_path=ground_truth, table1_csv_path=dblp_path, table2_csv_path=acm_path, attr_pair= pair,output_csv_path=f'{base_dir}/neg-all.csv',encoding='latin1')


def amazon_google_neg_generation():
    ground_truth='../data/amazon-google/Amzon_GoogleProducts_perfectMapping.csv'
    amazon_path = '../data/amazon-google/amazon.csv'
    google_path = '../data/amazon-google/google.csv'
    pair= ('id','id')
    generate_non_gt_pairs(gt_csv_path=ground_truth, table1_csv_path=amazon_path, table2_csv_path=google_path, attr_pair= pair,output_csv_path='../data/amazon-google/neg-all.csv',encoding='latin1')

def cora_neg_generation():
    ground_truth='../data/cora/cora_DPL.csv'
    cora_path = '../data/cora/cora.csv'
    pair= ('id','id')
    generate_non_gt_pairs(gt_csv_path=ground_truth, table1_csv_path=cora_path, table2_csv_path=cora_path, attr_pair= pair,output_csv_path='../data/cora/neg-all.csv')
    
def imdb_neg_generation():
    IMDB_PATH = f'../data/imdb/'
    name = IMDB_PATH+f'/name_basics.csv'
    title = IMDB_PATH+f'/title_basics.csv'
    t_gt = f'{IMDB_PATH}/title_basics_dups.csv'
    n_gt = f'{IMDB_PATH}/name_basics_dups.csv'
    t_pair= ('tconst','tconst')
    n_pair = ('nconst','nconst')
    generate_non_gt_pairs(gt_csv_path=t_gt, table1_csv_path=title, table2_csv_path=title, attr_pair= t_pair,output_csv_path=f'{ IMDB_PATH}/neg-all-title.csv')
    generate_non_gt_pairs(gt_csv_path=n_gt, table1_csv_path=name, table2_csv_path=name, attr_pair= n_pair,output_csv_path=f'{ IMDB_PATH}/neg-all-name.csv')


def poke_neg_generation():
    SPECIES = f'species' 
    SPECIES_NAME = f'spec_name'
    SPECIES_DESC = f'spec_desc'
    MOVE = f'move' 
    MOVE_NAME = f'move_name'
    MOVE_DESC = f'move_desc'
    POKE_PATH = f'../data/pokemon/'
    species_path = f'{POKE_PATH}species.csv'
    move_path = f'{POKE_PATH}{MOVE}.csv'
    species_gt= f'{POKE_PATH}species_dups.csv'
    move_gt= f'{POKE_PATH}move_dups.csv'
    
    t_pair= (f'{SPECIES}',f'{SPECIES}')
    n_pair = (f'{MOVE}',f'{MOVE}')
    generate_non_gt_pairs(gt_csv_path=species_gt, table1_csv_path=species_path, table2_csv_path=species_path, attr_pair= t_pair,output_csv_path=f'{ POKE_PATH}/neg-all-{SPECIES}.csv')
    generate_non_gt_pairs(gt_csv_path=move_gt, table1_csv_path=move_path, table2_csv_path=move_path, attr_pair= n_pair,output_csv_path=f'{ POKE_PATH}/neg-all-{MOVE}.csv')


def dblp_sampling(percent = 20 ):
    ground_truth='../data/dblp/dblp-id_acm-id.csv'
    pos_examples = csv_to_eqo_examples(ground_truth,True,percent)
    sample_len = len(pos_examples)
    all_neg = '../data/dblp/neg-all.csv'
    dblp_path = '../data/dblp/dblp.csv'
    acm_path = '../data/dblp/acm.csv'
    neg_examples = sample_negative_examples(all_neg, dblp_path, acm_path,size=sample_len,sim=utils.is_sim,m=1,attr_pairs=None,encoding ='ISO-8859-1' )
    print('\n'.join(list(pos_examples)+list(neg_examples)))
    
def dblp_acm_sampling_from_tuples(percent = 0.4, base_dir = '../data/dblp-acm', out_dir = '../data/dblp-acm' ):
    ground_truth='../data/dblp-acm/dblp-id_acm-id.csv'
    dblp_path = '../data/dblp-acm/dblp.csv'
    acm_path = '../data/dblp-acm/acm.csv'
    # pos_examples = csv_to_eqo_examples(ground_truth,True,percent)
    train_dblp,train_dblp_ids, test_dblp, test_dblp_ids = sample_csv_to_asp_facts(dblp_path,'ISO-8859-1',sample_ratio=percent, attr_prefix='d', sampled_csv_path=f'{out_dir}/dblp.csv')
    train_acm, train_acm_ids, test_acm, test_acm_ids = sample_csv_to_asp_facts(acm_path,'ISO-8859-1',sample_ratio=percent, attr_prefix='a', sampled_csv_path=f'{out_dir}/acm.csv')
    train_gt = pick_ground_truth_pairs(ground_truth,train_dblp_ids,train_acm_ids,encoding='ISO-8859-1',sampled_csv_path=f'{out_dir}/dblp-id_acm-id.csv')
    test_gt = pick_ground_truth_pairs(ground_truth,test_dblp_ids,test_acm_ids,encoding='ISO-8859-1')
    
    
    sample_len = len(train_gt)
    sim_defined = {('title','title',85), ('authors','authors',85), ('venue','venue',85)}
    all_neg = '../data/dblp-acm/neg-all.csv'
    # neg_examples = sample_negative_examples(train_gt, dblp_path, acm_path,size=sample_len,sim=utils.is_sim,m=1,attr_pairs={('title','title',0.5),('authors','authors',0.2),('venue','venue',0.2),('year','year',0.1)},encoding ='latin1',sim_defined=sim_defined,)
    neg_examples = sample_negative_examples4(train_gt, dblp_path, acm_path,size=sample_len,sim=utils.is_sim,entity_attrs=('id','id'),m=1,attr_pairs={('title','title',0.25),('authors','authors',0.25),('venue','venue',0.25),('year','year',0.25)},encoding ='ISO-8859-1',sim_defined=sim_defined,)
    # neg_examples = sample_negative_pairs4(dblp_path, acm_path, sample_len,exclude_attributes={'tid', 'id'}, all_negative_pairs_csv=all_neg, similarity_threshold= 65, encoding ='latin1',id_column=1 )

    # neg_examples = sample_negative_examples2(all_neg, dblp_path, acm_path,size=sample_len,sim=utils.is_sim,m=2,attr_pairs=None,encoding ='latin1',sim_defined=sim_defined )
    # print('\n'.join(list(pos_examples)+list(neg_examples)))
    return train_dblp|train_acm, train_gt|neg_examples, test_dblp|test_acm, test_gt
    
    
def dblp_gt(percent = 20 ):
    ground_truth='../data/dblp-acm/dblp-id_acm-id.csv'
    pos_examples = csv_to_eqo_examples(ground_truth,True,percent)
    sample_len = len(pos_examples)
    all_neg = '../data/dblp/neg-all.csv'
    dblp_path = '../data/dblp/dblp.csv'
    acm_path = '../data/dblp/acm.csv'
    # neg_examples = sample_negative_examples(all_neg, dblp_path, acm_path,size=sample_len,sim=utils.is_sim,m=1,attr_pairs=None,encoding ='ISO-8859-1' )
    print('\n'.join(list(pos_examples)))
    
def dblp_scholar_sampling(percent = 20 ):
    ground_truth='../data/dblp-scholar/DBLP-Scholar_perfectMapping.csv'
    dblp_path = '../data/dblp-scholar/dblp.csv'
    acm_path = '../data/dblp-scholar/scholar.csv'
    pos_examples = csv_to_eqo_examples(ground_truth,True,percent)
    sample_len = len(pos_examples)
    sim_defined = {('title','title'), ('authors','authors'), ('venue','venue')}
    all_neg = '../data/dblp-scholar/neg-all.csv'
    # neg_examples = sample_negative_examples(pos_examples, dblp_path, acm_path,size=sample_len,sim=utils.is_sim,m=2,attr_pairs=None,encoding ='latin1',sim_defined=sim_defined )
    neg_examples = sample_negative_pairs4(dblp_path, acm_path, sample_len,exclude_attributes={'tid', 'id'}, all_negative_pairs_csv=all_neg, similarity_threshold= 65, encoding ='latin1',id_column=1 )

    # neg_examples = sample_negative_examples2(all_neg, dblp_path, acm_path,size=sample_len,sim=utils.is_sim,m=2,attr_pairs=None,encoding ='latin1',sim_defined=sim_defined )
    print('\n'.join(list(pos_examples)+list(neg_examples)))
    
    
def dblp_scholar_sampling_from_tuples(percent = 0.4):
    ground_truth='../data/dblp-scholar/DBLP-Scholar_perfectMapping.csv'
    dblp_path = '../data/dblp-scholar/dblp.csv'
    acm_path = '../data/dblp-scholar/scholar.csv'
    # pos_examples = csv_to_eqo_examples(ground_truth,True,percent)
    train_dblp,train_dblp_ids, test_dblp, test_dblp_ids = sample_csv_to_asp_facts(dblp_path,'latin1',sample_ratio=percent, attr_prefix='d')
    train_scholar, train_scholar_ids, test_scholar, test_scholar_ids = sample_csv_to_asp_facts(acm_path,'latin1',sample_ratio=percent, attr_prefix='s')
    train_gt = pick_ground_truth_pairs(ground_truth,train_dblp_ids,train_scholar_ids,encoding='latin1')
    test_gt = pick_ground_truth_pairs(ground_truth,test_dblp_ids,test_scholar_ids,encoding='latin1')
    
    
    sample_len = len(train_gt)
    sim_defined = {('title','title',85), ('authors','authors',85), ('venue','venue',85)}
    all_neg = '../data/dblp-scholar/neg-all.csv'
    # neg_examples = sample_negative_examples(train_gt, dblp_path, acm_path,size=sample_len,sim=utils.is_sim,m=1,attr_pairs={('title','title',0.5),('authors','authors',0.2),('venue','venue',0.2),('year','year',0.1)},encoding ='latin1',sim_defined=sim_defined,)
    neg_examples = sample_negative_examples4(train_gt, dblp_path, acm_path,size=sample_len,sim=utils.is_sim,entity_attrs=('id','id'),m=1,attr_pairs={('title','title',0.25),('authors','authors',0.25),('venue','venue',0.25),('year','year',0.25)},encoding ='latin1',sim_defined=sim_defined,)
    # neg_examples = sample_negative_pairs4(dblp_path, acm_path, sample_len,exclude_attributes={'tid', 'id'}, all_negative_pairs_csv=all_neg, similarity_threshold= 65, encoding ='latin1',id_column=1 )

    # neg_examples = sample_negative_examples2(all_neg, dblp_path, acm_path,size=sample_len,sim=utils.is_sim,m=2,attr_pairs=None,encoding ='latin1',sim_defined=sim_defined )
    # print('\n'.join(list(pos_examples)+list(neg_examples)))
    return train_dblp|train_scholar, train_gt|neg_examples, test_dblp|test_scholar, test_gt


def dblp_scholar_sampling_from_tuples(percent = 0.4 , base_dir = '../data/dblp-scholar', out_dir = '../data/dblp-scholar'):
    ground_truth=f'{base_dir}/DBLP-Scholar_perfectMapping.csv'
    dblp_path = f'{base_dir}/dblp.csv'
    acm_path = f'{base_dir}/scholar.csv'
    # pos_examples = csv_to_eqo_examples(ground_truth,True,percent)
    train_dblp,train_dblp_ids, test_dblp, test_dblp_ids = sample_csv_to_asp_facts(dblp_path,'latin1',sample_ratio=percent, attr_prefix='d', sampled_csv_path=f'{out_dir}/dblp.csv')
    train_scholar, train_scholar_ids, test_scholar, test_scholar_ids = sample_csv_to_asp_facts(acm_path,'latin1',sample_ratio=percent, attr_prefix='s', sampled_csv_path=f'{out_dir}/scholar.csv')
    train_gt = pick_ground_truth_pairs(ground_truth,train_dblp_ids,train_scholar_ids,encoding='latin1', sampled_csv_path=f'{out_dir}/DBLP-Scholar_perfectMapping.csv')
    test_gt = pick_ground_truth_pairs(ground_truth,test_dblp_ids,test_scholar_ids,encoding='latin1')
    
    
    sample_len = len(train_gt)
    sim_defined = {('title','title',85), ('authors','authors',85), ('venue','venue',85)}
    all_neg = f'{base_dir}/neg-all.csv'
    # neg_examples = sample_negative_examples(train_gt, dblp_path, acm_path,size=sample_len,sim=utils.is_sim,m=1,attr_pairs={('title','title',0.5),('authors','authors',0.2),('venue','venue',0.2),('year','year',0.1)},encoding ='latin1',sim_defined=sim_defined,)
    neg_examples = sample_negative_examples4(train_gt, dblp_path, acm_path,size=sample_len,sim=utils.is_sim,entity_attrs=('id','id'),m=1,attr_pairs={('title','title',0.25),('authors','authors',0.25),('venue','venue',0.25),('year','year',0.25)},encoding ='latin1',sim_defined=sim_defined,)
    # neg_examples = sample_negative_pairs4(dblp_path, acm_path, sample_len,exclude_attributes={'tid', 'id'}, all_negative_pairs_csv=all_neg, similarity_threshold= 65, encoding ='latin1',id_column=1 )

    # neg_examples = sample_negative_examples2(all_neg, dblp_path, acm_path,size=sample_len,sim=utils.is_sim,m=2,attr_pairs=None,encoding ='latin1',sim_defined=sim_defined )
    # print('\n'.join(list(pos_examples)+list(neg_examples)))
    return train_dblp|train_scholar, train_gt|neg_examples, test_dblp|test_scholar, test_gt
    
def dblp_gt(percent = 20 ):
    ground_truth='../data/dblp-scholar/DBLP-Scholar_perfectMapping.csv'
    dblp_path = '../data/dblp-scholar/dblp.csv'
    acm_path = '../data/dblp-scholar/scholar.csv'
    pos_examples = csv_to_eqo_examples(ground_truth,True,percent)
    sample_len = len(pos_examples)
    # all_neg = '../data/dblp-scholar/neg-all.csv'
    # neg_examples = sample_negative_examples(all_neg, dblp_path, acm_path,size=sample_len,sim=utils.is_sim,m=1,attr_pairs=None,encoding ='latin1' )
    print('\n'.join(list(pos_examples)))
      
    
def amazon_google_sampling(percent = 20 ):
    ground_truth='../data/amazon-google/Amzon_GoogleProducts_perfectMapping.csv'
    amazon_path = '../data/amazon-google/amazon.csv'
    google_path = '../data/amazon-google/google.csv'
    pos_examples = csv_to_eqo_examples(ground_truth,True,percent)
    sample_len = len(pos_examples)
    all_neg = '../data/amazon-google/neg-all.csv'
    neg_examples = sample_negative_examples(all_neg, amazon_path, google_path,size=sample_len,sim=utils.is_sim,m=1,attr_pairs=None,encoding ='latin1' )
    print('\n'.join(list(pos_examples)+list(neg_examples)))
    
    
    
def amazon_google_gt(percent = 20 ):
    ground_truth='../data/amazon-google/Amzon_GoogleProducts_perfectMapping.csv'
    amazon_path = '../data/amazon-google/amazon.csv'
    google_path = '../data/amazon-google/google.csv'
    pos_examples = csv_to_eqo_examples(ground_truth,True,percent)
    sample_len = len(pos_examples)
    # all_neg = '../data/amazon-google/neg-all.csv'
    # neg_examples = sample_negative_examples(all_neg, amazon_path, google_path,size=sample_len,sim=utils.is_sim,m=1,attr_pairs=None,encoding ='latin1' )
    print('\n'.join(list(pos_examples)))

def cora_sampling(percent = 20 ):
    ground_truth='../data/cora/cora_DPL.csv'
    cora_path = '../data/cora/cora.csv'
    pos_examples = csv_to_eqo_examples(ground_truth,True,percent)
    sample_len = len(pos_examples)
    all_neg = '../data/cora/neg-all.csv'
    neg_examples = sample_negative_examples(all_neg, cora_path, cora_path,size=sample_len,sim=utils.is_sim,m=1,attr_pairs=None )
    print('\n'.join(list(pos_examples)+list(neg_examples)))
    
    
def cora_sampling_from_tuples(percent = 0.4,  base_dir = '../data/cora', out_dir = '../data/cora' ):
    ground_truth='../data/cora/cora_DPL.csv'
    dblp_path = '../data/cora/cora.csv'
    # acm_path = '../data/dblp-scholar/scholar.csv'
    # pos_examples = csv_to_eqo_examples(ground_truth,True,percent)
    train_cora,train_cora_ids, test_cora, test_cora_ids = sample_csv_to_asp_facts(dblp_path,encoding='ISO-8859-1',sample_ratio=percent,gt_att='id', sampled_csv_path=f'{out_dir}/cora.csv')
    # train_scholar, train_scholar_ids, test_scholar, test_scholar_ids = sample_csv_to_asp_facts(acm_path,'latin1',sample_ratio=percent, attr_prefix='s')
    train_gt = pick_ground_truth_pairs(ground_truth,train_cora_ids,train_cora_ids,encoding='ISO-8859-1',sampled_csv_path=f'{out_dir}/cora_DPL.csv')
    test_gt = pick_ground_truth_pairs(ground_truth,test_cora_ids,test_cora_ids,encoding='ISO-8859-1')
    
    
    
    sample_len = len(train_gt)
    sim_defined = {('address','address',90), ('authors','authors',85), ('booktitle','booktitle',90), ('date','date',95),('editor','editor',90)
                   ,('institution','institution',90),('journal','journal',90), ('pages','pages',95), ('publisher','publisher',90),
                   ('title','title',90),('volume','volume',95),('year','year',95)}
    # attr_pairs = {('address','address'), ('authors','authors'), ('booktitle','booktitle'), ('date','date'),('editor','editor')
    #                ,('institution','institution'),('journal','journal'),('month','month'),('note','note'),('pages','pages'), ('publisher','publisher'),
    #                ('tech','tech'),('title','title'),('type','type'),('volume','volume'),('year','year')}
    all_neg = '../data/dblp-scholar/neg-all.csv'
    # neg_examples = sample_negative_examples(train_gt, dblp_path, acm_path,size=sample_len,sim=utils.is_sim,m=1,attr_pairs={('title','title',0.5),('authors','authors',0.2),('venue','venue',0.2),('year','year',0.1)},encoding ='latin1',sim_defined=sim_defined,)
    neg_examples = sample_negative_examples4(train_gt, dblp_path, dblp_path,size=sample_len,sim=utils.is_sim,attr_pairs=None,entity_attrs=('id','id'),m=1,encoding ='ISO-8859-1',sim_defined=sim_defined,)
    # neg_examples = sample_negative_pairs4(dblp_path, acm_path, sample_len,exclude_attributes={'tid', 'id'}, all_negative_pairs_csv=all_neg, similarity_threshold= 65, encoding ='latin1',id_column=1 )

    # neg_examples = sample_negative_examples2(all_neg, dblp_path, acm_path,size=sample_len,sim=utils.is_sim,m=2,attr_pairs=None,encoding ='latin1',sim_defined=sim_defined )
    # print('\n'.join(list(pos_examples)+list(neg_examples)))
    return train_cora, train_gt|neg_examples, test_cora, test_gt    

def cddb_sampling_from_tuples(percent = 0.4,  base_dir = '../data/cddb', out_dir = '../data/cddb' ):
    ground_truth='../data/cddb/cddb_DPL.csv'
    dblp_path = '../data/cddb/cddb.csv'
    # acm_path = '../data/dblp-scholar/scholar.csv'
    # pos_examples = csv_to_eqo_examples(ground_truth,True,percent)
    train_cora,train_cora_ids, test_cora, test_cora_ids = sample_csv_to_asp_facts(dblp_path,encoding='ISO-8859-1',sample_ratio=percent,gt_att='id', sampled_csv_path=f'{out_dir}/cddb.csv')
    # train_scholar, train_scholar_ids, test_scholar, test_scholar_ids = sample_csv_to_asp_facts(acm_path,'latin1',sample_ratio=percent, attr_prefix='s')
    train_gt = pick_ground_truth_pairs(ground_truth,train_cora_ids,train_cora_ids,encoding='ISO-8859-1',sampled_csv_path=f'{out_dir}/cddb_DPL.csv')
    test_gt = pick_ground_truth_pairs(ground_truth,test_cora_ids,test_cora_ids,encoding='ISO-8859-1')
    
    
    
    sample_len = len(train_gt)
    sim_defined = {('artist','artist',90), ('category','category',90), ('genre','genre',90),('title','title',90),('track','track',85)}
    # sim_defined = {('address','address',90), ('authors','authors',85), ('booktitle','booktitle',90), ('date','date',95),('editor','editor',90)
    #                ,('institution','institution',90),('journal','journal',90), ('pages','pages',95), ('publisher','publisher',90),
    #                ('title','title',90),('volume','volume',95),('year','year',95)}
    # attr_pairs = {('address','address'), ('authors','authors'), ('booktitle','booktitle'), ('date','date'),('editor','editor')
    #                ,('institution','institution'),('journal','journal'),('month','month'),('note','note'),('pages','pages'), ('publisher','publisher'),
    #                ('tech','tech'),('title','title'),('type','type'),('volume','volume'),('year','year')}
    all_neg = '../data/dblp-scholar/neg-all.csv'
    # neg_examples = sample_negative_examples(train_gt, dblp_path, acm_path,size=sample_len,sim=utils.is_sim,m=1,attr_pairs={('title','title',0.5),('authors','authors',0.2),('venue','venue',0.2),('year','year',0.1)},encoding ='latin1',sim_defined=sim_defined,)
    neg_examples = sample_negative_examples4(train_gt, dblp_path, dblp_path,size=sample_len,sim=utils.is_sim,attr_pairs=None,entity_attrs=('id','id'),m=1,encoding ='ISO-8859-1',sim_defined=sim_defined,)
    # neg_examples = sample_negative_pairs4(dblp_path, acm_path, sample_len,exclude_attributes={'tid', 'id'}, all_negative_pairs_csv=all_neg, similarity_threshold= 65, encoding ='latin1',id_column=1 )

    # neg_examples = sample_negative_examples2(all_neg, dblp_path, acm_path,size=sample_len,sim=utils.is_sim,m=2,attr_pairs=None,encoding ='latin1',sim_defined=sim_defined )
    # print('\n'.join(list(pos_examples)+list(neg_examples)))
    return train_cora, train_gt|neg_examples, test_cora, test_gt    


    
def cora_gt(percent = 20 ):
    ground_truth='../data/cora/cora_DPL.csv'
    cora_path = '../data/cora/cora.csv'
    pos_examples = csv_to_eqo_examples(ground_truth,True,percent)
    sample_len = len(pos_examples)
    # all_neg = '../data/cora/neg-all.csv'
    # neg_examples = sample_negative_examples(all_neg, cora_path, cora_path,size=sample_len,sim=utils.is_sim,m=1,attr_pairs=None )
    print('\n'.join(list(pos_examples)))
    


def imdb_sampling_from_tuples(percent = 0.4 , base_dir = '../data/imdb', out_dir = '../data/imdb/title'):
    ground_truth=f'{base_dir}/title_basics_dups.csv'
    title_path = f'{base_dir}/title_basics.csv'
    title_aka_path = f'{base_dir}/title_akas.csv'
    title_ratings_path = f'{base_dir}/title_ratings.csv'

    # pos_examples = csv_to_eqo_examples(ground_truth,True,percent)
    train_title,train_title_ids, test_title, test_title_ids = sample_csv_to_asp_facts(title_path,'utf-8',sample_ratio=percent,sampled_csv_path=f'{out_dir}/title_basics.csv',gt_att='tconst')
    train_akas, test_akas = from_csv_to_asp_facts(title_aka_path,train_title_ids,test_title_ids,gt_att='titleId',sampled_csv_path=f'{out_dir}/title_akas.csv')
    train_ratings, test_ratings = from_csv_to_asp_facts(title_ratings_path,train_title_ids,test_title_ids,gt_att='tconst',sampled_csv_path=f'{out_dir}/title_ratings.csv')

    # train_scholar, train_scholar_ids, test_scholar, test_scholar_ids = sample_csv_to_asp_facts(acm_path,'utf-8',sample_ratio=percent)
    train_gt = pick_ground_truth_pairs(ground_truth,train_title_ids,train_title_ids,encoding='utf-8',sampled_csv_path=f'{out_dir}/title_basics_dups.csv')
    test_gt = pick_ground_truth_pairs(ground_truth,test_title_ids,test_title_ids,encoding='utf-8')
    
    
    sample_len = len(train_gt)
    sim_defined = {('titleType','titleType',90), ('primaryTitle','primaryTitle',85) ,('genres','genres',90)
                   ,('title','title',85)}
    # attr_pairs = {('address','address'), ('authors','authors'), ('booktitle','booktitle'), ('date','date'),('editor','editor')
    #                ,('institution','institution'),('journal','journal'),('month','month'),('note','note'),('pages','pages'), ('publisher','publisher'),
    #                ('tech','tech'),('title','title'),('type','type'),('volume','volume'),('year','year')}
    all_neg = '../data/imdb/neg-all-title.csv'
    related_csvs = [('titleId', title_aka_path), ('tconst', title_ratings_path)]
    neg_examples = sample_negative_examples_multi(train_gt, title_path, title_path,related_csvs=related_csvs,size=sample_len,sim=utils.is_sim,attr_pairs=None,entity_attrs=('tconst','tconst'),m=1,encoding ='utf-8',sim_defined=sim_defined,to_skip={'isAdult','isOriginalTitle','originalTitle'})
    return train_title|train_akas|train_ratings, train_gt|neg_examples, test_title|test_akas|test_ratings, test_gt  


def poke_sampling_from_tuples(percent = 0.4 , base_dir = '../data/pokemon', out_dir = '../data/pokemon'):
    ground_truth=f'{base_dir}/species_dups.csv'
    species_path = f'{base_dir}/species.csv'
    species_name_path = f'{base_dir}/spec_name.csv'
    species_desc_path = f'{base_dir}/spec_desc.csv'

    # pos_examples = csv_to_eqo_examples(ground_truth,True,percent)
    train_species,train_species_ids, test_species, test_species_ids = sample_csv_to_asp_facts(species_path,'utf-8',sample_ratio=percent,sampled_csv_path=f'{out_dir}/species.csv',gt_att='species')
    train_akas, test_akas = from_csv_to_asp_facts(species_name_path,train_species_ids,test_species_ids,gt_att='species',sampled_csv_path=f'{out_dir}/spec_name.csv')
    train_ratings, test_ratings = from_csv_to_asp_facts(species_desc_path,train_species_ids,test_species_ids,gt_att='species',sampled_csv_path=f'{out_dir}/spec_desc.csv')

    # train_scholar, train_scholar_ids, test_scholar, test_scholar_ids = sample_csv_to_asp_facts(acm_path,'utf-8',sample_ratio=percent)
    train_gt = pick_ground_truth_pairs(ground_truth,train_species_ids,train_species_ids,encoding='utf-8',sampled_csv_path=f'{out_dir}/species_dups.csv')
    test_gt = pick_ground_truth_pairs(ground_truth,test_species_ids,test_species_ids,encoding='utf-8')
    
    
    sample_len = len(train_gt)
    sim_defined = {('name','name',90), ('genus','genus',90) ,('flavor_text','flavor_text',85)}
    # attr_pairs = {('address','address'), ('authors','authors'), ('bookspecies','bookspecies'), ('date','date'),('editor','editor')
    #                ,('institution','institution'),('journal','journal'),('month','month'),('note','note'),('pages','pages'), ('publisher','publisher'),
    #                ('tech','tech'),('species','species'),('type','type'),('volume','volume'),('year','year')}
    all_neg = '../data/poke/neg-all-species.csv'
    related_csvs = [('species', species_name_path), ('species', species_desc_path)]
    neg_examples = sample_negative_examples_multi(train_gt, species_path, species_path,related_csvs=related_csvs,size=sample_len,sim=utils.is_sim,attr_pairs=None,entity_attrs=('species','species'),m=1,encoding ='utf-8',sim_defined=sim_defined, to_skip={'evolves_from_species', 'evolution_chain'})
    return train_species|train_akas|train_ratings, train_gt|neg_examples, test_species|test_akas|test_ratings, test_gt  

def imdb_sampling(percent = 20 ):
    ground_truth='../data/imdb/name_basics_dups.csv'
    cora_path = '../data/imdb/name_basics.csv'
    pos_examples = csv_to_eqo_examples(ground_truth,True,percent)
    sample_len = len(pos_examples)
    all_neg = '../data/imdb/neg-all-name.csv'
    neg_examples = sample_negative_examples(all_neg, cora_path, cora_path,size=sample_len,sim=utils.is_sim,m=1,attr_pairs=None )
    print('\n'.join(list(pos_examples)+list(neg_examples)))
    # sim_facts = utils.load_cache('./cache/sim-dblpter.pkl')
    
def imdb_gt(percent = 20 ):
    ground_truth='../data/imdb/title_basics_dups.csv'
    cora_path = '../data/imdb/title_basics.csv'
    pos_examples = csv_to_eqo_examples(ground_truth,True,percent)
    sample_len = len(pos_examples)
    # all_neg = '../data/imdb/neg-all-name.csv'
    # neg_examples = sample_negative_examples(all_neg, cora_path, cora_path,size=sample_len,sim=utils.is_sim,m=1,attr_pairs=None )
    neg_examples = sample_negative_examples4(train_gt, dblp_path, dblp_path,size=sample_len,sim=utils.is_sim,attr_pairs=None,entity_attrs=('id','id'),m=1,encoding ='ISO-8859-1',sim_defined=sim_defined,)

    print('\n'.join(list(pos_examples)))
    # sim_facts = utils.load_cache('./cache/sim-dblpter.pkl')

def poke_species_sampling(percent = 20 ):
    SPECIES = f'species' 
    SPECIES_NAME = f'spec_name'
    SPECIES_DESC = f'spec_desc'
    MOVE = f'move' 
    MOVE_NAME = f'move_name'
    MOVE_DESC = f'move_desc'
    POKE_PATH = f'../data/pokemon/'
    species_path = f'{POKE_PATH}species.csv'
    ground_truth= f'{POKE_PATH}species_dups.csv'

    pos_examples = csv_to_eqo_examples(ground_truth,True,percent)
    sample_len = len(pos_examples)
    all_neg = f'{POKE_PATH}neg-all-{SPECIES}.csv'
    neg_examples = sample_negative_examples(all_neg, species_path, species_path,size=sample_len,sim=utils.is_sim,m=2,attr_pairs=None )
    print('\n'.join(list(pos_examples)+list(neg_examples)))

def write(facts, path):
    # filepath = os.path.join(directory, filename)
    # Make sure the directory exists
    # os.makedirs(directory, exist_ok=True)
    # Write the set of strings to the file
    with open(path, "w", encoding="utf-8") as f:
        for line in facts:
            f.write(line + "\n")  # add newline after each string
            
def save_facts (dataname,split, directory,samples, sub_dir='', sample_num = '', sub_num = ''):   
    dic = os.path.join(directory,dataname,str(split)) if is_empty(sub_dir) else os.path.join(directory,dataname,sub_dir,str(split)) 
    dic = os.path.join(dic,sample_num) if not is_empty(sample_num) else dic 
    dic =  os.path.join(dic,sub_num) if  not is_empty(sub_num) else dic 
    train_bk_path = os.path.join(dic,f'train-bk-{split}.lp')
    train_gt_path = os.path.join(dic,f'train-gt-{split}.lp')
    test_bk_path = os.path.join(dic,f'test-bk-{split}.lp')
    test_gt_path = os.path.join(dic,f'test-gt-{split}.lp')
    train_bk = list(sorted(samples[0]))
    train_gt = list(sorted(samples[1]))
    test_bk = list(sorted(samples[2]))
    test_gt = list(sorted(samples[3]))
    write(train_bk,train_bk_path)
    write(train_gt,train_gt_path)
    write(test_bk,test_bk_path)
    write(test_gt,test_gt_path)
    
    
def clean_value(v: str) -> str:
    return v.strip().strip('"').strip("'")

def extract_pairs_from_asp_file(asp_file: str) -> List[Tuple[str, str]]:
    """
    Extract (c1, c2) pairs from a single ASP file containing facts like:
        pos(eqo("c1","c2")).
        neg(eqo("c1","c2")).
    """

    pattern = re.compile(
        r'^(?:pos|neg)\(eqo\("([^"]+)","([^"]+)"\)\)\.$'
    )

    pairs = []

    with open(asp_file, 'r', encoding='utf-8', errors='ignore') as f:
        for line in f:
            line = line.strip()

            if not line:
                continue

            match = pattern.match(line)
            if match:
                c1, c2 = match.groups()
                pairs.append((c1, c2))
            else:
                # Debug (you can remove after confirming it works)
                print("NO MATCH:", repr(line))

    print(f"Extracted {len(pairs)} pairs")
    print("Sample:", pairs[:5])

    return pairs

def save_positive_pairs_from_asp(
    asp_file: str,
    output_csv: str,
    encoding: str = "utf-8"
):
    """
    Extract positive eqo pairs from an ASP file and save to CSV.

    Output CSV columns: c1, c2
    """

    pattern = re.compile(
        r'^(pos|neg)\(eqo\("([^"]+)","([^"]+)"\)\)\.$'
    )

    pos_pairs = []

    with open(asp_file, 'r', encoding=encoding, errors='ignore') as f:
        for line in f:
            line = line.strip()
            if not line:
                continue

            match = pattern.match(line)
            if match:
                label, c1, c2 = match.groups()
                if label == "pos":
                    pos_pairs.append((c1, c2))
            else:
                # optional debug
                print("NO MATCH:", repr(line))

    print(f"Extracted {len(pos_pairs)} positive pairs")

    # Save to CSV
    df = pd.DataFrame(pos_pairs, columns=["c1", "c2"])
    df.to_csv(output_csv, index=False, encoding=encoding)

    print(f"Saved positive pairs to {output_csv}")

def extract_records_from_csv(
    asp_dir: str,
    csv_paths: Union[str, List[str]],
    column_names: Union[str, Tuple[str, str]],
    output_dir: str,
    encoding: Union[str, Tuple[str, str], List[str]] = "utf-8"
):
    """
    Parameters:
    - asp_dir: directory containing ASP ground truth files
    - csv_paths: one path or list of two paths to CSV files
    - column_names:
        - if single CSV: str
        - if two CSVs: tuple (col1, col2)
    - output_dir: directory to save results
    - encoding:
        - str → same encoding for all CSVs
        - tuple/list of length 2 → per-file encodings
    """

    os.makedirs(output_dir, exist_ok=True)
    pairs = extract_pairs_from_asp_file(asp_dir)

    # Normalize encoding
    if isinstance(encoding, str):
        encodings = [encoding, encoding]
    else:
        encodings = list(encoding)
        if len(encodings) == 1:
            encodings = encodings * 2
        elif len(encodings) != 2:
            raise ValueError("encoding must be a string or a list/tuple of length 1 or 2.")

    # Case 1: Single CSV
    if isinstance(csv_paths, str):
        df = pd.read_csv(csv_paths, encoding=encodings[0])
        col = column_names

        values = set([c for pair in pairs for c in pair])
        filtered_df = df[df[col].astype(str).isin(values)]

        out_path = os.path.join(output_dir, "matched_records.csv")
        filtered_df.to_csv(out_path, index=False, encoding=encodings[0])
        print(f"Saved combined records to {out_path}")

    # Case 2: Two CSVs
    elif isinstance(csv_paths, list) and len(csv_paths) == 2:
        df1 = pd.read_csv(csv_paths[0], encoding=encodings[0], dtype=str)
        df2 = pd.read_csv(csv_paths[1], encoding=encodings[1], dtype=str)

        col1, col2 = column_names

        c1_values = set(c1 for c1, _ in pairs)
        c2_values = set(c2 for _, c2 in pairs)

        filtered_df1 = df1[df1[col1].astype(str).isin(c1_values)]
        filtered_df2 = df2[df2[col2].astype(str).isin(c2_values)]

        out1 = os.path.join(output_dir, "matched_c1.csv")
        out2 = os.path.join(output_dir, "matched_c2.csv")

        filtered_df1.to_csv(out1, index=False, encoding=encodings[0])
        filtered_df2.to_csv(out2, index=False, encoding=encodings[1])

        print(f"Saved c1 records to {out1}")
        print(f"Saved c2 records to {out2}")

    else:
        raise ValueError("csv_paths must be either a string or a list of two paths.")

import csv
import os
import re


def process_csv(csv_path):
    """
    Process a CSV file without changing numeric formatting.

    Rules:
    1. If a row has first-column value: rec-{tid}-dup-0
       then delete rows whose first-column value is: id-{tid}

    2. Replace first-column values:
         rec-{tid}-dup-0 -> {tid}
         id-{tid}        -> {tid}

    3. Preserve all other column values exactly as they appear
       (avoids pandas float conversion issues).

    4. Save result as: originalname_d.csv
    """

    with open(csv_path, "r", newline="", encoding="utf-8") as f:
        reader = csv.reader(f)
        rows = list(reader)

    if not rows:
        raise ValueError("CSV file is empty.")

    header = rows[0]
    data_rows = rows[1:]

    # Find tids from rec-{tid}-dup-0
    rec_pattern = re.compile(r"^rec-(.+)-dup-0$")

    tids_to_remove = set()

    for row in data_rows:
        if not row:
            continue

        value = row[0]
        match = rec_pattern.match(value)

        if match:
            tids_to_remove.add(match.group(1))

    # Remove rows with id-{tid}
    remove_ids = {f"id-{tid}" for tid in tids_to_remove}

    processed_rows = []

    for row in data_rows:
        if not row:
            continue

        first_value = row[0]

        # Skip rows to remove
        if first_value in remove_ids:
            continue

        # Convert first column to tid only
        match = re.match(r"^rec-(.+)-dup-0$", first_value)
        if match:
            row[0] = match.group(1)
        else:
            match = re.match(r"^id-(.+)$", first_value)
            if match:
                row[0] = match.group(1)

        processed_rows.append(row)

    # Output path
    base, ext = os.path.splitext(csv_path)
    output_path = f"{base}_d{ext}"

    # Write output CSV
    with open(output_path, "w", newline="", encoding="utf-8") as f:
        writer = csv.writer(f)
        writer.writerow(header)
        writer.writerows(processed_rows)

    print(f"Processed file saved to: {output_path}")

    return output_path
import csv
import os


def clean_table_file(file_path, null_threshold=0.9, encoding = 'utf-8'):
    """
    Clean a CSV/TSV file by:
      1. Dropping columns with null percentage >= threshold
      2. Dropping columns containing only a single distinct value
      3. Adding a unique 'tid' column as the first column
      4. Saving result as a new CSV file

    Original values are preserved exactly (no float conversion).

    Parameters
    ----------
    file_path : str
        Path to input CSV or TSV file.

    null_threshold : float
        Null percentage threshold (default=0.9 for 90%).

    Returns
    -------
    str
        Path to saved cleaned CSV file.
    """

    # Detect delimiter
    ext = os.path.splitext(file_path)[1].lower()

    if ext == ".csv":
        delimiter = ","
    elif ext == ".tsv":
        delimiter = "\t"
    else:
        raise ValueError("Input file must be .csv or .tsv")

    # Read file
    with open(file_path, "r", encoding=encoding, newline="") as f:
        reader = csv.reader(f, delimiter=delimiter)
        rows = list(reader)

    if not rows:
        raise ValueError("File is empty")

    header = rows[0]
    data_rows = rows[1:]

    num_rows = len(data_rows)
    num_cols = len(header)

    # Ensure all rows have same length
    normalized_rows = []

    for row in data_rows:
        padded_row = row + [""] * (num_cols - len(row))
        normalized_rows.append(padded_row[:num_cols])

    # ------------------------------------------------------------
    # Count nulls and distinct values
    # ------------------------------------------------------------
    null_counts = [0] * num_cols
    distinct_values = [set() for _ in range(num_cols)]

    for row in normalized_rows:

        for i, value in enumerate(row):

            value = value.strip()

            if value == "":
                null_counts[i] += 1
            else:
                distinct_values[i].add(value)

    # ------------------------------------------------------------
    # Determine columns to keep
    # ------------------------------------------------------------
    keep_indices = []

    for i in range(num_cols):

        null_percentage = (
            null_counts[i] / num_rows if num_rows > 0 else 0
        )

        num_distinct = len(distinct_values[i])

        # Keep only if:
        #   - null percentage < threshold
        #   - more than one distinct non-null value
        if (
            null_percentage < null_threshold
            and num_distinct > 1
        ):
            keep_indices.append(i)

    # ------------------------------------------------------------
    # Build cleaned table
    # ------------------------------------------------------------
    cleaned_rows = []

    cleaned_header = ["tid"] + [header[i] for i in keep_indices]
    cleaned_rows.append(cleaned_header)

    for tid, row in enumerate(normalized_rows):

        cleaned_row = [row[i] for i in keep_indices]

        cleaned_rows.append([str(tid)] + cleaned_row)

    # ------------------------------------------------------------
    # Save output
    # ------------------------------------------------------------
    base_name = os.path.splitext(file_path)[0]
    output_path = f"{base_name}_cleaned.csv"

    with open(output_path, "w", encoding=encoding, newline="") as f:
        writer = csv.writer(f)
        writer.writerows(cleaned_rows)

    print(f"Original columns: {num_cols}")
    print(f"Remaining columns: {len(keep_indices)}")
    print(f"Number of tuples: {num_rows}")
    print(f"Saved cleaned file to: {output_path}")

    return output_path



def tsv_to_csv(tsv_path,encoding = 'utf-8'):
    """
    Convert a TSV file to a CSV file.

    Parameters
    ----------
    tsv_path : str
        Path to input TSV file.

    Returns
    -------
    str
        Path to generated CSV file.
    """

    if not tsv_path.lower().endswith(".tsv"):
        raise ValueError("Input file must be a .tsv file")

    # Output path
    csv_path = os.path.splitext(tsv_path)[0] + ".csv"

    # Read TSV and write CSV
    with open(tsv_path, "r", encoding=encoding, newline="") as tsv_file, \
         open(csv_path, "w", encoding=encoding, newline="") as csv_file:

        reader = csv.reader(tsv_file, delimiter="\t")
        writer = csv.writer(csv_file)

        for row in reader:
            writer.writerow(row)

    print(f"Saved CSV file to: {csv_path}")

    return csv_path

if __name__ == "__main__":
    # pokemon_species_atoms()
    #rel_name_1 = 'area'
    #rel_name_2 = 'area'
    #df1 =  f'./dataset/music/50/{rel_name_1}_c.csv'
    #df2 = f'./dataset/music/50/{rel_name_2}_c.csv'
    #attr1 = 'area_type'
    #attr2 = 'area_type'
    # dblp_neg_generation()
    # dblp_acm.update(sims)
    #dblp_scholar_atoms()
    # amazon_google_atoms()
    # dblp_scholar_neg_generation('./lp/dblp-scholar/80')
    
    # amazon_google_neg_generation()
    # cora_sampling(40)
    # cora_atoms()
    # [print(n) for n in load_gt_fact('../data/imdb/name_basics_dups.csv',is_positive=True)]
    # poke_neg_generation()
    # imdb_atoms()
    # cora_sampling_from_tuples(0.4)

    
    # save_facts('dblp','80','./lp/',dblp_acm_sampling_from_tuples(0.8))
    # dblp_path = '../data/dblp-scholar/dblp.csv'
    # acm_path = '../data/dblp-scholar/scholar.csv'
    # extract_records_from_csv(
    # asp_dir="./lp/dblp-scholar/80/s1/exs.pl",
    # csv_paths=[dblp_path,acm_path],
    # column_names=["id","id"],
    # output_dir="./lp/dblp-scholar/80",
    # encoding= ['latin1','latin1']
    # )
    # save_positive_pairs_from_asp(  asp_file="./lp/dblp-scholar/80/s1/exs.pl" , encoding='latin1',output_csv="./lp/dblp-scholar/80/DBLP-Scholar_perfectMapping.csv",)
    # [print(n) for n in csv_to_eqo_examples('../data/imdb/name_basics_dups.csv',True,40)]
    # cora_neg_generation()
    # dblp_scholar_sampling_from_tuples(0.5)
    # 3208/3574 0.9
    # 8259/
    # x 
    # 0.6 * d / 0.8 * d 
    # save_facts('cora','80','./lp/',cora_sampling_from_tuples(0.8, out_dir='./lp/cora/80/s4'))
    # save_facts('cora','80','./lp/',cora_sampling_from_tuples(0.8, out_dir='./lp/cora/80/s5'))
    # save_facts('dblp-scholar','80','./lp/',dblp_scholar_sampling_from_tuples(0.8,base_dir='./lp/dblp-scholar/80/s4', out_dir='./lp/dblp-scholar/80/s4/v5'))
    # s = [1,2,3,4,5]
    # v06 = [1,2,3,4,5]
    # percent = [0.2]
    # for p in percent:
    #     for _s in s:
    #         for _v in v06:
    #             print(f'=================s{str(_s)} v{str(_v)} ===============')
    #             save_facts('dblp-scholar',f'{str(p)}','./lp/',dblp_scholar_sampling_from_tuples(p, base_dir=f'./lp/dblp-scholar/80/s{_s}',out_dir=f'./lp/dblp-scholar/{str(p)}/s{str(_s)}/v{str(_v)}'),sample_num=f's{str(_s)}', sub_num=f'v{str(_v)}')
    
    
    # s = [1,2,3,4,5]
    # v = [1,2,3,4,5]
    # percent = [0.2]
    # for p in percent:
    #     for _s in s:
    #         for _v in v:
    #             print(f'=================s{str(_s)} v{str(_v)} ===============')
    #             save_facts('cora',f'{str(p)}','./lp/',cora_sampling_from_tuples(p, base_dir=f'./lp/cora/80/s{_s}',out_dir=f'./lp/cora/{str(p)}/s{str(_s)}/v{str(_v)}'),sample_num=f's{str(_s)}', sub_num=f'v{str(_v)}')
    # save_facts('imdb','80','./lp/',imdb_sampling_from_tuples(0.8, out_dir='./lp/imdb/80/s2'),sample_num='s2')
    # save_facts('imdb','0.6','./lp/',imdb_sampling_from_tuples(0.6, base_dir= './lp/imdb/80/s2', out_dir='./lp/imdb/0.6/s2/v3'),sample_num=f's2', sub_num=f'v3')

    # save_facts('dblp-scholar','0.4','./lp/',dblp_scholar_sampling_from_tuples(0.4,base_dir='./lp/dblp-scholar/80/s4',out_dir='./lp/dblp-scholar/0.4/s4/v4'),sample_num=f's4', sub_num=f'v4')

    # s = [1,2,3,4,5]
    # v06 = [1,2,3,4,5]
    # percent = [0.2]
    # for p in percent:
    #     for _s in s:
    #         for _v in v06:
    #             print(f'=================s{str(_s)} v{str(_v)} ===============')
    #             save_facts('imdb',f'{str(p)}','./lp/',imdb_sampling_from_tuples(p, base_dir=f'./lp/imdb/80/s{_s}',out_dir=f'./lp/imdb/{str(p)}/s{str(_s)}/v{str(_v)}'),sample_num=f's{str(_s)}', sub_num=f'v{str(_v)}')
    # process_csv('../data/pokemon/spec_name-crpt.csv')
    # save_facts('pokemon',f'0.8','./lp/',poke_sampling_from_tuples(0.8, base_dir=f'./lp/pokemon/80/s1', out_dir=f'./lp/pokemon/0.8/s1/v2'),sample_num=f's1',sub_num=f'v2')

    percent = 0.2
    s = [1,2,3,4,5]
    for _s in s:
        v = [1,2,3,4,5]
        for _v in v:
            save_facts('pokemon',f'{str(percent)}','./lp/',poke_sampling_from_tuples(percent, base_dir=f'./lp/pokemon/80/s{str(_s)}', out_dir=f'./lp/pokemon/{str(percent)}/s{str(_s)}/v{str(_v)}'),sample_num=f's{str(_s)}',sub_num=f'v{_v}')
    # clean_table_file('../data/cddb/cddb.tsv',null_threshold=1,encoding='ISO-8859-1')
    # tsv_to_csv('../data/cddb/cddb_DPL.tsv',encoding='ISO-8859-1')
    # s = [1,2,3,4,5]
    # for _s in s:
        # v = [1,2,3,4,5]
        # for _v in v:
        #     save_facts('cddb',f'80','./lp/',cddb_sampling_from_tuples(0.8, base_dir=f'./lp/cddb/80/s4', out_dir=f'./lp/cddb/80/s4/v{_v}'),sample_num=f's4',sub_num=f'v{_v}')
    # cddb_atoms()