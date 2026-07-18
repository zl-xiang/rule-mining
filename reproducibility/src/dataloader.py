from importlib.resources import path
from typing import Sequence
import pandas as pd
from pandas import DataFrame
import os
import xml.etree.ElementTree as et
import utils


UTF8 = 'utf-8'
ISO = 'ISO-8859-1'

STRING = 0
NUM = 1
LST = 2



def load_csv( encoding = 'utf-8', path_list = []):
    assert len(path_list) >0
    #print(path_list[0])
    sep = ',' if '.tsv' not in path_list[0] else '\t'
    #print(sep)
    tbls = dict()
    for path in path_list:
        t_name = path.replace('.tsv','').replace('.csv','').split('/')[-1]
        t_name = t_name[:-2] if t_name.endswith('_c') else t_name
        tbls[t_name] = pd.read_csv(path,encoding=encoding, sep=sep,dtype=str)
    return tbls


def save_gts(splits:dict,name:str)->None:
    gt_frame = {k:pd.DataFrame(columns=[1,2]) for k,v in splits.items()}
    for k,v in splits.items():
        splits_dicts = list()
        v = utils.remove_symmetry(v) # [2023-05-21] generated name GTs are now transtivly and symmertically closed
        for _v in v:
            if not _v[0] == _v[1]:
                splits_dicts.append({1:_v[0],2:_v[1]})
        pd.concat([gt_frame[k],pd.DataFrame(splits_dicts)],ignore_index=True).to_csv(f"./dataset/imdb/{name}_{str(k)}.csv",sep=",",encoding="utf-8",index=False)

def drop_columns(df:DataFrame, columns:Sequence[str],out_dir):
    df = df.drop(columns=columns,axis=1)
    df.to_csv(out_dir,index=False,sep=",",encoding="utf-8",)
    
    
def atom2df(atoms, df: DataFrame, token, outdir='./dataset/imdb'):
        frame = pd.DataFrame(columns=df.columns)     
        # partion_dict = {k:pd.DataFrame(columns=v.columns) for k,v in data}
        parts = list()
        pred = ''
        for a in atoms:
            # print(a)
            pred = utils.REL_PAT.findall(a)[0]
            # print(pred,token)
            if utils.is_empty(token):
                pred = pred[:-1]    
            else: pred = pred.replace(f'_{token}','').replace(f'_c{token}','')
            #print(pred)
            val_lst = utils.VAR_PAT.findall(a)[0]
            # print(val_lst)
            val_lst = val_lst.split('","')
            val_lst = [utils.process_atom_val(v) for v in val_lst]
            # print(val_lst)
            col = frame.columns
            row = dict()
            for i,c in enumerate(col):
                # print(pred,c,i,len(val_lst),val_lst)
                row[c] = val_lst[i]
            parts.append(row)
        # print(partion_dict.keys())
        frame = pd.concat([frame,pd.DataFrame(parts)],ignore_index=True)
            # print(v)
        frame.to_csv(f"{outdir}/{pred}_{token}.csv",sep=",",encoding=UTF8,index=False)
        
      
def load_ground_truth(ground_truth_path:list, encoding =UTF8):
        paths = ground_truth_path
        tbl = load_csv(path_list=paths,encoding=encoding)
        
        def add_truth(_tbl):
            truth_lst = list()
            for row_idx, _ in _tbl.iterrows():
                t = []
                for c_idx, col in enumerate(_tbl.columns):
                    t.append(str(_tbl.iat[row_idx,c_idx]))
                t = *t,
                if len(t) >2:
                    t = ((t[2],t[3]),(t[4],t[5]))
                #_t = (t[1],t[0])
                truth_lst.append(tuple(t))
            return truth_lst       
        if not isinstance(tbl,list):
            return add_truth(tbl)
        else:
            gt_set = dict()
            for t in tbl:
                gt_set[ t[0].replace('_dups','')] = add_truth(_tbl=t[1])
            #reversed_truth_set.add(tuple(_t))
            return gt_set #,reversed_truth_set
        
# File names of the form {relation_1}-{attribute_1}_{relation_2}-{attribute_2}.csv       
def load_examples(ground_truth_path:list, encoding =UTF8):
        paths = ground_truth_path
        tbl = load_csv(path_list=paths,encoding=encoding)
        
        def add_truth(_tbl):
            truth_lst = list()
            for row_idx, _ in _tbl.iterrows():
                t = []
                for c_idx, col in enumerate(_tbl.columns):
                    t.append(str(_tbl.iat[row_idx,c_idx]))
                t = *t,
                truth_lst.append(tuple(t))
            return truth_lst       
        gt_set = dict()
        for pname,gt in tbl.items():
            gt_set[pname] = add_truth(_tbl=gt)
        #reversed_truth_set.add(tuple(_t))
        return gt_set #,reversed_truth_set
    

class Dataloader:
    def __init__(self, path_list=None,  ground_truth = [],encoding=UTF8):
        # name of default dataset
        self.encoding = encoding
            # directories of the pair of tables
        self.path_list = []
        self.ground_truth = ''
        self.path_list = path_list
        self.ground_truth = ground_truth
    

    def load(self,):
        csv = self.load_data()
        return csv

    
    def load_data (self,):
        assert self.path_list !=None     
        # encoding = 'ISO-8859-1'if self.name == DBLP_ACM else 'utf-8'
        return load_csv(path_list=self.path_list,encoding=self.encoding) 
    
    def load_ground_truth(self, encoding = UTF8):
        return load_ground_truth(ground_truth_path=self.ground_truth,encoding=encoding)
    
    def load_examples(self, encoding = UTF8):
        return load_examples(ground_truth_path=self.ground_truth,encoding=encoding)
    
    def load_local_truth(self,encoding = UTF8):
        return load_ground_truth(ground_truth_path=self.local_ground_truth,encoding=encoding)
    
    def ground_truth_stats(self):
        gt = self.load_ground_truth()
        if isinstance(gt,list):
            print(" * Ground truth size:",len(gt))
        else:
            size = 0
            for k,v  in gt.items():
                size+= len(v)
            print(" * Ground truth size:",size)
           
    def gt_to_atom(self,gts=None):
        gt_atoms = set()
        gt_pred = 'gt'
        for k,v in gts.items():
            for tup in v:
                t1 = f'"{tup[0]}"'
                t2 = f'"{tup[1]}"'
                atom_1 = utils.get_atom_(pred_name=gt_pred,tup=[k,t1])
                atom_2 = utils.get_atom_(pred_name=gt_pred,tup=[k,t2])
                gt_atoms.add(atom_1)
                gt_atoms.add(atom_2)
        return gt_atoms
    
    def fgt_to_atom(self,cs=None,k=None):
        c_atoms = set()
        c_pred = 'gt'
        # print(cs)
        for tup in cs:
            t1 = f'"{tup[0]}","{tup[1]}"'
            atom_1 = utils.get_atom_(pred_name=c_pred,tup=[k,t1])
            c_atoms.add(atom_1)
        return c_atoms

def count_records_with_value(csv_file_path, column_name, value):
    df = pd.read_csv(csv_file_path)
    count = len(df[df[column_name] == value])
    return count

def remove_records_and_save_copy(csv_file_path, column_name, values):
    # Read the CSV file into a DataFrame
    df = pd.read_csv(csv_file_path)

    # Remove records where the specified column matches any of the given values
    df_filtered = df[df[column_name].isin(values)]

    # Create a new filename for the modified CSV file
    file_name, file_extension = os.path.splitext(csv_file_path)
    new_file_path = f"{file_name}_.csv"

    # Save the modified DataFrame to the new CSV file
    df_filtered.to_csv(new_file_path, index=False)
    
def modify_and_save_column(csv_file_path, column_name):
    def format_numeric(val):
        if isinstance(val, (int, float)):
            return f'{val:.0f}'
        return val
    # Read the CSV file into a DataFrame
    df = pd.read_csv(csv_file_path,dtype=str)
   
    # Convert the DataFrame to string data type
   # df = df.astype(str)

    # Modify values in the specified column
    df[column_name] = df[column_name].apply(lambda x: 'id-' + x if pd.notnull(x) and x != 'nan' else x)
    df.applymap(format_numeric) 
    # Save the modified DataFrame back to the original CSV file
    df.to_csv(csv_file_path, index=False,float_format='%.0f')


def modify_csv(df1_file, col_name, df2_file, dir):
    # Read the CSV files into pandas DataFrames
    df1 = pd.read_csv(df1_file)
    df2 = pd.read_csv(df2_file)
    
    # Merge df1 with df2 based on the 'id' column
    merged_df = pd.merge(df1, df2, left_on=col_name, right_on='id', how='left')
    print(merged_df.columns)
    # Replace the values in col_name with the corresponding values from the 'name' column of df2
    merged_df[col_name] = merged_df['name'].fillna(merged_df[col_name])
    
    # Drop the 'id' and 'name' columns as they are no longer needed
    merged_df.drop(columns=df2.columns, inplace=True)
    
    # Save the resulting DataFrame to a CSV file in the specified directory
    output_file = os.path.join(dir, 'result.csv')
    merged_df.to_csv(output_file, index=False)
    

def find_joins_and_save(df1_file, df2_file, attr1, attr2, output_file):
    # Read the CSV files into pandas DataFrames
    df1 = pd.read_csv(df1_file)
    df2 = pd.read_csv(df2_file)
    rel_name1 = df1.columns[0]
    rel_name2 = df2.columns[0]
    
    # Merge df1 with df2 based on attr1 and attr2
    merged_df = pd.merge(df1, df2, left_on=attr1, right_on=attr2, how='left', suffixes=('1', '2'))
    print(merged_df.columns)
    # Filter out rows where the join attributes have the same value
    if rel_name1 == rel_name2:
        merged_df = merged_df[merged_df[f'{rel_name1}1'] != merged_df[f'{rel_name2}2']]
        
     
    # Save the resulting DataFrame to a CSV file
    merged_df.to_csv(output_file, index=False)
    
def find_joins_and_save(df1_file, df2_file, attr1, attr2, output_file):
    # Read the CSV files into pandas DataFrames
    df1 = pd.read_csv(df1_file)
    df2 = pd.read_csv(df2_file)
    rel_name1 = df1.columns[0]
    rel_name2 = df2.columns[0]
    # Forward merge df1 with df2 based on attr1 and attr2
    merged_df_forward = pd.merge(df1, df2, left_on=attr1, right_on=attr2, how='inner', suffixes=('1', '2'))
    merged_df_forward.columns = [f'{df1_file[:-4]},{rel_name1}1', attr1, f'{df2_file[:-4]},{rel_name2}2', attr2]
    
    # Backward merge df2 with df1 based on attr2 and attr1
    merged_df_backward = pd.merge(df2, df1, left_on=attr2, right_on=attr1, how='inner', suffixes=('1', '2'))
    merged_df_backward.columns = [f'{df2_file[:-4]},{rel_name2}2', attr2, f'{df1_file[:-4]},{rel_name1}1', attr1]
    
    # Concatenate both DataFrames
    result_df = pd.concat([merged_df_forward, merged_df_backward])
    
    # Drop duplicate rows
    result_df.drop_duplicates(inplace=True)
    
    # Save the resulting DataFrame to a CSV file
    result_df.to_csv(output_file, index=False)
    
    
def add_index_column(input_file, output_dir):
    # Read the CSV file into pandas DataFrame
    df = pd.read_csv(input_file)
    
    # Add an extra column named 'index' with integer-valued index starting from 1
    df['index'] = range(1, len(df) + 1)
    
    # Save the new DataFrame to a CSV file in the specified directory
    # output_file = os.path.join(output_dir, 'output.csv')
    df.to_csv(output_dir, index=False)
    print(f"DataFrame with index column saved to {output_dir}")
