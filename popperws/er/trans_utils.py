
import re
import utils
from pathlib import Path

DEF_OPERA_PAT = re.compile(r'(\s*(?:=|!=|>=|<=)\s*)', re.IGNORECASE) 

CACHE_DIR = './cache'

### matching patterns ### 
ATOM_PAT =  utils.ATOM_PAT
VAR_PAT = utils.VAR_PAT
REL_PAT = utils.REL_PAT
EQUATE_PAT = utils.EQUATE_PAT
# if any variables in equate pattern have #count coocurrance, shall be exluded
# COUNT_PAT = re.compile(r"(([A-Z0-9]+)(?:\s*=|>=|<=|>|<\s*))?#count\{[^}]*\}((?:\s*=|>=|<=|>|<\s*)([A-Z0-9]+))?", re.IGNORECASE)
COUNT_PAT = utils.COUNT_PAT
# inside of brackets of count pattern should be separated by ";", counjuncts are the rest of strings concat by ":"
# TODO:
SIM_THRESH_PAT = utils.SIM_THRESH_PAT
SIM_THRESH_VAL_PAT =utils.SIM_THRESH_VAL_PAT
SIM_JOIN_PAT = utils.SIM_JOIN_PAT
SPEC_CHAR_PAT = utils.SPEC_CHAR_PAT
EQ_AC_PAT = utils.EQ_AC_PAT
EQ_AC_AT_PAT = utils.EQ_AC_AT_PAT

SINGLE_VAR_PAT = r'[A-Za-z0-9]+'

CONST_PAT = r'^"[^"]*"|[a-z0-9]+$'
QUOATED_CONST_PAT = r'"[^"]*"'
### matching patterns ### 

### data processing ####
SEP_COMMA = ','
SEP_AND = ' and '
SEP_AMP = ' & '
DF_EMPTY = 'nan'
SEP_LST = [SEP_COMMA,SEP_AMP,SEP_AND] 

META = "meta_"
REL_PRED = f'{META}rel'
SCHEMA_PRED = f'{META}schema'
ATTR_PRED = f'{META}attr'
REL_ATTR_MAP = f'{META}rel_attr_map'
TUPLE_PRED = 't'
CONST_PRED = 'c'
### data processing ####

### asp symbols ###
### predicates
SIM_PRED = "sim"
SIM_FUNC_PRED = '@' + SIM_PRED
EQ_PRED = "eq"
UP_EQ = "up_eq"


### LACE+ 
EQO_PRED = "eqo"
NEQO_PRED = "neqo"
EQV_PRED = "eqv"
NEQV_PRED = "neqv"
ACTIVE_O_PRED = "activeo"
ACTIVE_V_PRED = "activev"
PROJ_PRED = "proj"
VAL_PRED = "val"



### TRC
ATT_PRED = "att"


MOCK_DC_PRED = 'falsify'
ACTIVE_PRED = "active"
TO_BE_SIM ='sim_attr'
TO_SIM ='to_sim'
ACTIVE_DOM = 'adom'
UP_EQ = 'up_eq'
NEQ_PRED = 'neq'
COUNT_DIRC = '#count'
EXTERNAL_DIRC = '#external'


### default symbols
DEFAULT_NEG = 'not'
IMPLY = ':-'
SHOW = '#show'
PROGRAM = '#program'
DOT = '.'
ANOMY_VAR = "_"
NOT_EQUAL = '!='
EQUAL = '='
LEQ = '<='
LESS = '<'
GEQ = '>='
GREATER = '>'

BUILT_INS = {NOT_EQUAL, EQUAL,LEQ,LESS,GEQ,GREATER}

BUILT_INS_PAT = r'([A-Za-z0-9]+|"[^"]*")\s*(?:!=|=|<=|<|>=|>)\s*([A-Za-z0-9]+|"[^"]*")'

### default rules
EQ_AXIOMS = f"""
{EQ_PRED}(X,Y) {IMPLY} {EQ_PRED}(X,Z),{EQ_PRED}(Z,Y).
{EQ_PRED}(X,Y) {IMPLY} {EQ_PRED}(Y,X).
"""
EQ_AXIOMS_TER = f"""
{EQ_PRED}(X,Y,I) {IMPLY} {EQ_PRED}(X,Z,I),{EQ_PRED}(Z,Y,I).
{EQ_PRED}(X,Y,I) {IMPLY} {EQ_PRED}(Y,X,I).
"""

EQ_AXIOMS_VLOG_TRANS_TER = f"""
{EQ_PRED}(?X,?Y,?I) {IMPLY} {EQ_PRED}(?X,?Z,?I),{EQ_PRED}(?Z,?Y,?I).
"""

EQ_AXIOMS_VLOG_SYM_TER = f"""
{EQ_PRED}(?X,?Y,?I) {IMPLY} {EQ_PRED}(?Y,?X,?I).
"""


ACTIVE_CHOICE = f"""
{{{EQ_PRED}(X,Y)}} {IMPLY} {ACTIVE_PRED}(X,Y).
"""

ACTIVE_CHOICE_TER = f"""
{{{EQ_PRED}(X,Y,I)}} {IMPLY} {ACTIVE_PRED}(X,Y,I).
"""

SIM_TGRS = """sim(X,Y,S) :- sim(Y,X,S). 
sim(X,X,100) :- sim(X,X,_)."""
ADOM_TGRS = """eq(X,X) :- adom(X)."""
EMPTY_TGRS = """empty(nan). empty("nan").empty("ーーー")."""
### asp symbols ###


### trace annotations ###
ANTD_SHOW_TRACE = '%!show_trace'
ANTD_TRACE_ATOM = '%!trace'
ANTD_TRACE_RULE = '%!trace_rule'

SYMM_DESC = 'is symmetrically closed by'
TRANS_DESC = 'is transitivly closed by'

EQ_AXIOMS_TRACE = f"""
{ANTD_TRACE_RULE}{{"(%,%) {SYMM_DESC} (%,%)", X,Y,X,Y,Y,X}}.
{EQ_PRED}(X,Y){IMPLY}{EQ_PRED}(Y,X).
{ANTD_TRACE_RULE}{{"(%,%) {TRANS_DESC} (%,%) - (%,%) ", X,Z,X,Y,Y,Z}}.
{EQ_PRED}(X,Z){IMPLY}{EQ_PRED}(X,Y),{EQ_PRED}(Y,Z).
"""

EQ_AXIOMS_TER_TRACE = f"""
{ANTD_TRACE_RULE}{{"(%,%) {TRANS_DESC} (%,%) - (%,%)", X,Z,X,Y,Z,Y}}.
{EQ_PRED}(X,Y,I) {IMPLY} {EQ_PRED}(X,Z,I),{EQ_PRED}(Z,Y,I).
{ANTD_TRACE_RULE}{{"(%,%) {SYMM_DESC} (%,%) ", X,Y,X,Y,Y,X}}.
{EQ_PRED}(X,Y,I) {IMPLY} {EQ_PRED}(Y,X,I).
"""
# 1
EQ_AXIOMS_REC = f"""
{EQ_PRED}(X,Y,I) {IMPLY} {EQ_PRED}(X,Z,I),{EQ_PRED}(Z,Y,I1), I1<=I, I<i.
{EQ_PRED}(X,Y,I) {IMPLY} {EQ_PRED}(Y,X,I).
"""
# 2
EQ_AXIOMS_REC_ = f"""
{EQ_PRED}(X,Y,i) {IMPLY} {EQ_PRED}(X,Z,i-1),{EQ_PRED}(Z,Y,I), I<i.
{EQ_PRED}(X,Y,I) {IMPLY} {EQ_PRED}(Y,X,I).
"""
#3
_EQ_AXIOMS_REC = f"""
{EQ_PRED}(X,Y,i-1) {IMPLY} {EQ_PRED}(X,Z,i-1),{EQ_PRED}(Z,Y,I), I<i.
{EQ_PRED}(X,Y,I) {IMPLY} {EQ_PRED}(Y,X,I).
"""
#1
EQ_AXIOMS_REC_TER = f"""
{EQ_PRED}(X,Y,A,I) {IMPLY} {EQ_PRED}(X,Z,A,I),{EQ_PRED}(Z,Y,A,I1), I1<=I, I<i.
{EQ_PRED}(X,Y,A,I) {IMPLY} {EQ_PRED}(Y,X,A,I).
"""
#2
EQ_AXIOMS_REC_TER_ = f"""
{EQ_PRED}(X,Y,A,i) {IMPLY} {EQ_PRED}(X,Z,A,i-1),{EQ_PRED}(Z,Y,A,I), I<i.
{EQ_PRED}(X,Y,A,I) {IMPLY} {EQ_PRED}(Y,X,A,I).
"""
#3 in use
_EQ_AXIOMS_REC_TER = f"""
{EQ_PRED}(X,Y,A,i) {IMPLY} {EQ_PRED}(X,Z,A,i),{EQ_PRED}(Z,Y,A,I),I<i.
{EQ_PRED}(X,Y,A,I) {IMPLY} {EQ_PRED}(Y,X,A,I).
"""

MEQ_REC = f'm{EQ_PRED}(X,Y,i) {IMPLY} {EQ_PRED}(X,Y,i), {EQ_PRED}(X,Y).'
MEQ_REC_TER = f'm{EQ_PRED}(X,Y,A,i) {IMPLY} {EQ_PRED}(X,Y,A,i), {EQ_PRED}(X,Y,A).'

ITER_READOFF = 'eqm(X,Y,A,I) :- eq(X,Y,A,I), eq(X,Y,A).' 


# TODO: to modify here
TRACE_EQ = f'{ANTD_SHOW_TRACE} {{{EQ_PRED}(X,Y)}}.'
# TODO: to modify here
TRACE_EQ_TER = f'{ANTD_SHOW_TRACE} {{{EQ_PRED}(X,Y,I)}}.'
TRACE_PAIR = f'{ANTD_SHOW_TRACE} {{{EQ_PRED}(^,^)}}.'
TRACE_PAIR_TER = f'{ANTD_SHOW_TRACE} {{{EQ_PRED}(^,^,^)}}.'
### trace annotations ###



### LACE+ axioms

EQUIV_CELL_SET = f'{VAL_PRED}(T1,I1,V) {IMPLY} {EQV_PRED}(T1,I1,T2,I2), {PROJ_PRED}(T2,I2,V){DOT}'

EQV_SYMMETRY = f'{EQV_PRED}(T1,I1,T2,I2) {IMPLY} {EQV_PRED}(T2,I2,T1,I1){DOT}'
EQV_TRANSITIVITY = f'{EQV_PRED}(T1,I1,T2,I2) {IMPLY} {EQV_PRED}(T1,I1,T3,I3), {EQV_PRED}(T3,I3,T2,I2){DOT}'

EQO_SYMMETRY = f'{EQO_PRED}(X,Y) {IMPLY} {EQO_PRED}(Y,X){DOT}'
EQO_TRANSITIVITY = f'{EQO_PRED}(X,Y) {IMPLY} {EQO_PRED}(X,Z),{EQO_PRED}(Z,Y){DOT}'

ACTIVE_EQV = f'{{{EQV_PRED}(T1,I1,T2,I2)}} {IMPLY} {ACTIVE_V_PRED}(T1,I1,T2,I2){DOT}'
ACTIVE_EQO = f'{{{EQO_PRED}(X,Y)}} {IMPLY} {ACTIVE_O_PRED}(X,Y){DOT}'
### LACE+ axioms


HEAD = 'head'
BODIES = 'BODIES'

EQ_RELS = [EQO_PRED, EQV_PRED, EQ_PRED]

NOT_NULL_LITERAL = r'not empty\(([A-Z0-9]+)\)|([A-Z0-9]+)\s*!=\s*nan|nan\s*!=\s*([A-Z0-9]+)'



def get_rule_list(dir:str) -> list:
    rule_list:list[str] = []
    constraint_list:list[str] = []
    label_list:list[tuple[int,str]] = []
    show_list:list[str] = []
    rule = ""
    comment_pat = re.compile(r"\s*%.*\s*", re.IGNORECASE)
    with open(dir,'r', encoding='utf-8',
                 errors='ignore') as f:
        for line in  f.readlines():
            line = line.strip('\n')
            if line not in ['','\n','\t','\r'] and not comment_pat.match(line): # TODO: update to symbol API
                line = comment_pat.sub('', line)
                # print(line)
                #if (line.startswith("eq(") or line.startswith("active(")) or (rule.startswith("eq(") or rule.startswith("active(")): 
                line = line.replace('\r', '').replace('\n', '').replace('\t','')
                if not line.startswith("#"):
                    line = re.sub(r"(?<!not)\s+",'',line)
                rule += line
                if line.endswith("."):
                    if not rule.startswith(IMPLY) and not rule.startswith('#') and IMPLY in rule:
                        rule_list.append(rule)
                    elif not rule.startswith('#') and rule.startswith(IMPLY):
                        constraint_list.append(rule)
                    elif rule.startswith('#show'):
                        show_list.append(rule)
                    rule = ""
            elif comment_pat.match(line) and line.strip().startswith('%!'): # labels are only single-lines
                # if its rule label, check how many rules collected already
                # assign the label with the index of the rule
                label_list.append((len(rule_list),line.strip()))
        return rule_list, constraint_list, label_list, show_list

def get_sim_pairs(dir:str, sim_predname=SIM_PRED)-> dict:
    spec =  get_rule_list(dir)
    rules = spec[0]
    constraints = spec[1]
    rule_list = rules + constraints
    sim_pairs = dict()
    for i, r in enumerate(rule_list): 
        atoms = ATOM_PAT.findall(r)
        sims = [a for a in atoms if a.startswith(SIM_PRED) or a.startswith(sim_predname)]
        # simed relation name, sim occurring position
        if len(sims)>0:
            sim_threshs = SIM_THRESH_PAT.findall(r)
            if sim_threshs == None or len(sim_threshs)<1:
                continue
            sim_threshs = {ATOM_PAT.findall(s)[0]:int(SIM_THRESH_VAL_PAT.findall(s)[0]) for s in sim_threshs}
            for s in sims:
                svs = VAR_PAT.findall(s)[0].split(',')
                thresh = sim_threshs[s]
                vs_lst = list()
                for a in atoms:
                    pred_name = REL_PAT.findall(a)[0]
                    if pred_name != SIM_PRED and pred_name != sim_predname and pred_name!=EQ_PRED and pred_name!=ACTIVE_PRED and pred_name!='c':
                        a_vars = VAR_PAT.findall(a)[0].split(',')
                        [vs_lst.append((pred_name,a_vars.index(sv))) for sv in svs if sv in a_vars]                
                print(s)
                vs_lst = vs_lst[0] + vs_lst[1]
                if vs_lst not in sim_pairs:
                    sim_pairs[vs_lst] = thresh
                elif sim_pairs[vs_lst] > int(thresh):
                    sim_pairs[vs_lst] = int(thresh)
    return sim_pairs


def get_atom_vars(atom:str)->list[str]:
    #print(atom, VAR_PAT.findall(atom))
    return VAR_PAT.findall(atom)[0].split(',')

def get_atom_pred(atom:str)->str:
    _atom = REL_PAT.findall(atom)
    if len(_atom)>0:
        return _atom[0]
    else: 
        return ''

def get_atoms(cnj:str,)->list[str]:
    return ATOM_PAT.findall(cnj)


def locate_var_from_atoms(vname:str, atoms:list[str])-> tuple[str,int]:
    for a in atoms:
        #print(a)
        a_pred = REL_PAT.findall(a)[0]
        a_vars:list = get_atom_vars(a)
        if vname in a_vars and a_pred not in EQ_RELS and a_pred != 'empty':
            return a_pred,a_vars.index(vname)
        
def locate_var_from_atoms_tid(vname:str, atoms:list[str])-> tuple[str,int]:
    for a in atoms:
        a_pred = REL_PAT.findall(a)[0]
        a_vars:list = get_atom_vars(a)
        if vname in a_vars and a_pred not in EQ_RELS and a_pred != 'empty':
            return a_vars[0],a_vars.index(vname)
        
def locate_trc_att_from_atoms(vname:str, atoms:list[str])-> tuple[str,str]:
    for a in atoms:
        a_pred = REL_PAT.findall(a)[0]
        a_vars:list = get_atom_vars(a)
        if vname in a_vars:
            if a_pred == ATT_PRED:
                tid_var = a_vars[0]
                att_name = a_vars[1]
                rel_name = locate_var_from_atoms(tid_var,atoms)[0]
            elif a_pred != 'empty' and a_pred != SIM_PRED:
                rel_name = a_pred
                att_name = 'tid'
            return rel_name,att_name

def locate_body_var(vname:str,body:str)-> tuple[str,int]:
    atoms = get_atoms(body)
    return locate_var_from_atoms(vname,atoms)

def locate_trc_body_var(vname:str,body:str)-> tuple[str,str]:
    atoms = get_atoms(body)
    return locate_trc_att_from_atoms(vname,atoms)
        
def locate_body_var_from_literals(vname:str,body_literals:list[str])-> tuple[str,int]:
    atoms = [a if not a.startswith(DEFAULT_NEG) else a.replace(DEFAULT_NEG,'',1).strip() for a in body_literals]
    rel_atoms = [a for a in atoms if REL_PAT.match(a) and not a.startswith(SIM_PRED)]
    #print(rel_atoms)
    return locate_var_from_atoms(vname,rel_atoms)

# [added 20250424] resolving val atoms on variables participating similarity joins cell arguments weren't translated properly
def locate_body_var_from_literals_tid(vname:str,body_literals:list[str])-> tuple[str,int]:
    atoms = [a if not a.startswith(DEFAULT_NEG) else a.replace(DEFAULT_NEG,'',1).strip() for a in body_literals]
    rel_atoms = [a for a in atoms if REL_PAT.match(a) and not a.startswith(SIM_PRED)]
    return locate_var_from_atoms_tid(vname,rel_atoms)
        

def locate_body_var_pos(vname:str,body:str)-> tuple[str,int]:
    atoms = get_atoms(body)
    for a in atoms:
        a_pred = REL_PAT.findall(a)[0]
        a_vars:list = get_atom_vars(a)
        if vname in a_vars and  a_pred not in EQ_RELS:
            return a_vars[0],a_vars.index(vname)
        
def locate_body_var_pos_all(vname:str,body:str)-> list[tuple[str,int]]:
    atoms = get_atoms(body)
    occurances = list()
    for a in atoms:
        a_pred = REL_PAT.findall(a)[0]
        a_vars:list = get_atom_vars(a)
        tid_var = a_vars[0]
        if vname in a_vars and  a_pred not in EQ_RELS and a_pred != SIM_PRED:
            occurances.append((tid_var,a_vars.index(vname))) # no need to minus one for tid as the attributes counted from 1
    return occurances

def is_required_empty_var(vname:str, body_literals:list[str])->bool:
    required_empty_list = [l for l in body_literals if l.startswith('empty')]
    if len(required_empty_list)<1:
        return False
    else:
        check = [l for l in required_empty_list if vname in get_atom_vars(l)[0].strip()]
        return len(check)>0
    
"""
@input list of body literals
@output a dictionary contains join variables in the bodies as indices and the # of occurances as values 
"""        
def get_body_joins(literals:list[str] = [])-> dict[str,int]:
    body_var_dict = dict()
    for l in literals:
        if not l.startswith(DEFAULT_NEG):
            l_pred = get_atom_pred(l) # update here
            if not utils.is_empty(l_pred) and l_pred!= SIM_PRED and l_pred != 'empty':
                l_vars:list = get_atom_vars(l)
                #print(l_vars)
                for v in l_vars:
                    if v[0].isupper():
                        if not v in body_var_dict:
                            body_var_dict[v] = 1
                        else: 
                            body_var_dict[v]+=1
    
    body_joins_dict = {k:v for k,v in body_var_dict.items() if v>1}

    return body_joins_dict

def get_distinguished_vars(literals:list[str] = [])-> set:
    body_var_dict = dict()
    for l in literals:
        if l.startswith(DEFAULT_NEG):
          l = l.replace(DEFAULT_NEG,'').strip()  
        l_pred = get_atom_pred(l)
        if not utils.is_empty(l_pred):
            l_vars:list = get_atom_vars(l)
        else:
            l_vars = [v.strip() for v in  re.split(DEF_OPERA_PAT, l) if v not in {'=', '!=', '>=', '<='}]
        for v in l_vars:
            v = v.strip()
            # print(v)
            if str(v[0]).isupper():
                if not v in body_var_dict:
                    body_var_dict[v] = 1
                else: 
                    body_var_dict[v]+=1
            
    
    body_distinct_dict = {k:v for k,v in body_var_dict.items() if v==1 and k[0].isupper()}
    return set(body_distinct_dict.keys())

def get_merge_attributes(dir:str):
    rule_list:list[str] = get_rule_list(dir)[0]
    merge_attrs = dict()
    # check rule head variables
    for r in rule_list:
        r = r.split(IMPLY,1)
        h = r[0]
        b = r[1]
        if h.startswith(EQ_PRED) or h.startswith(ACTIVE_PRED) or h.startswith(EQO_PRED) or h.startswith(ACTIVE_O_PRED):
            merge_vars = get_atom_vars(h)
            #print(merge_vars)
            # iterate rule body to locate occurring relation
            x = locate_body_var(merge_vars[0],b)
            #print(x)
            y = locate_body_var(merge_vars[1],b)
            #print(y)
            if x != None and y != None:
                if x[0] not in merge_attrs:
                    merge_attrs[x[0]] = set()
                merge_attrs[x[0]].add(x[1])
                if y[0] not in merge_attrs:
                    merge_attrs[y[0]] = set()
                merge_attrs[y[0]].add(y[1])
    # merge_attrs.pop(EQ_PRED)
    return merge_attrs     

def get_merge_attributes_local(dir:str):
    rule_list:list[str] = get_rule_list(dir)[0]
    merge_o_attrs = dict()
    merge_v_attrs = dict()
    #print(rule_list)
    # check rule head variables
    for r in rule_list:
        r = r.split(IMPLY,1)
        h = r[0]
        # print(h)
        b = r[1]
        merge_vars = get_atom_vars(h)
        # print(h)
        if h.startswith(EQO_PRED) or h.startswith(ACTIVE_O_PRED):
            #print(merge_vars)
            # iterate rule body to locate occurring relation
            x = locate_body_var(merge_vars[0],b)
            #print(x)
            y = locate_body_var(merge_vars[1],b)
            #print(y)
            if x != None and y != None:
                if x[0] not in merge_o_attrs:
                    merge_o_attrs[x[0]] = set()
                merge_o_attrs[x[0]].add(x[1])
                if y[0] not in merge_o_attrs:
                    merge_o_attrs[y[0]] = set()
                merge_o_attrs[y[0]].add(y[1])
        elif h.startswith(EQV_PRED) or h.startswith(ACTIVE_V_PRED): 
            t1_rel = locate_body_var(merge_vars[0],b)[0]
            t2_rel = locate_body_var(merge_vars[2],b)[0]
            pos1 = merge_vars[1]
            pos2 = merge_vars[3]
            if t1_rel not in merge_v_attrs:
                merge_v_attrs[t1_rel] = set()
            merge_v_attrs[t1_rel].add(int(pos1))
            if t2_rel not in merge_v_attrs:
                merge_v_attrs[t2_rel] = set()
            merge_v_attrs[t2_rel].add(int(pos2))
    # print(merge_o_attrs)
    # merge_attrs.pop(EQ_PRED)
    return merge_o_attrs, merge_v_attrs    




def get_attr_types(lp_file_path):
    """
    Parse a .lp file and collect attr(a,rname,pos,er_type) atoms.

    Args:
        lp_file_path (str | Path): Path to .lp configuration file

    Returns:
        dict: {(rname, pos): er_type}
    """
    lp_file_path = Path(lp_file_path)

    if not lp_file_path.exists() or lp_file_path.suffix != ".lp":
        raise ValueError("Input must be an existing .lp file")
    
    pattern = re.compile(
        r"attr\s*\(\s*[^,\s]+\s*,\s*"   # a7 (ignored)
        r"[^,\s]+\s*,\s*"               # aname (ignored)
        r"([^,\s]+)\s*,\s*"             # rname
        r"([^,\s]+)\s*,\s*"             # pos
        r"([^,\s]+)\s*\)\s*\."          # er_type
    )

    result = {}

    with lp_file_path.open("r", encoding="utf-8") as f:
        for line in f:
            line = line.strip()
            if not line or line.startswith("%"):
                continue

            match = pattern.search(line)
            if match:
                rname, pos, er_type = match.groups()
                result[(rname, int(pos))] = int(er_type)

    return result


def remove_eqs(body_str:str) -> str:
    p_1 = r'(\s*)?eq\(([^,]+),([^,]+)\)(,\s*)?'
    p_2 = r'(\s*)?(not)(\s*)eq\(([^,]+),([^,]+)\)(,\s*)?'
    removed = re.sub(p_1,'',body_str)
    if removed.endswith(',.'):
        removed = removed[:-2]+'.'
    return removed

def get_body_literals(body_str:str) -> list[str]:
    body_literals = re.split(r',\s*(?![^()]*\))', body_str)
    literals = [literal.strip() for literal in body_literals]
    literals[-1] = literals[-1][:-1] if literals[-1].endswith('.') else literals[-1]
    return literals

def get_rule_parts(r:str) -> tuple[str,list[str]]:
    r_split = r.split(IMPLY,1)
    h = r_split[0].strip()
    b_literals = get_body_literals(r_split[1])
    return h,b_literals


def make_rule_body(body_literals: list[str])-> str:
    return ','.join(body_literals)

def make_normal_rule(head:str, body_literals:list[str])-> str:
    h = head
    b = make_rule_body(body_literals)
    return f'{h} {IMPLY} {b}.'


def get_ground_atom_args(ground_atom:str)->list[str]:
    # Regular expression pattern to match strings quoted by " and numbers
    pattern = r'"(?:[^"\\]|\\.)*"|[-+]?[0-9]*\.?[0-9]+(?:[eE][-+]?[0-9]+)?|nan'

    # Find all matches of the pattern in the input string
    matches = re.findall(pattern, ground_atom)

    # Remove the quotes from string arguments
    # matches = [arg.strip('"') for arg in matches]

    return matches

def anonymise_body(rule) -> str:
    h,b_literals = get_rule_parts(rule)
    if utils.is_empty(h):
        distinguished_vars = get_distinguished_vars(b_literals)
    else:
        distinguished_vars = get_distinguished_vars([h]+b_literals)

    new_body_lit_cp = b_literals.copy()
    for i,bl in enumerate(new_body_lit_cp):
        if bl.startswith(DEFAULT_NEG) :
            # print(b_pred)
            bl = bl.replace(DEFAULT_NEG,'').strip()
        b_pred = get_atom_pred(bl)

        if not utils.is_empty(b_pred):
            b_vars = get_atom_vars(bl)
            for j,bv in enumerate(b_vars.copy()):
                if bv in distinguished_vars:
                    b_vars[j] = ANOMY_VAR
            anonmyed_bl = utils.get_atom(b_pred,tuple(b_vars))
            if b_literals[i].startswith(DEFAULT_NEG): anonmyed_bl= f'{DEFAULT_NEG} {anonmyed_bl}'
            b_literals[i] = anonmyed_bl
    new_r = make_normal_rule(h,b_literals)
    return new_r

def match_not_null_var(literal:str) -> str:
     # Search for the pattern in the input string
    matches = re.findall(NOT_NULL_LITERAL, literal)
    if not len(matches) <1:
        return matches[0] 


def match_builtin_vars(literal:str) -> tuple[str]:
     # Search for the pattern in the input string
    matches = re.findall(BUILT_INS_PAT, literal)
    if not len(matches) <3:
        return tuple[matches] 
    
def match_constant(literal:str)->bool:
    matches = re.match(CONST_PAT,literal)
    if matches:
        return True
    else:
        return False

def extract_arguments(atom:str)->list[str]:
    # Define the regex pattern
    pattern = r'[A-Za-z0-9_]+\((.*)\)'
    
    # Match the pattern in the input string
    match = re.match(pattern, atom)
    
    if not match:
        return None  # Return None if the input string does not match the pattern
    
    # Extract the full match (the argument list part)
    argument_list = match.group(1)
    
    # Define a regex pattern to extract each argument
    arg_pattern = r'([A-Z0-9]+|"[^"]*"|[a-z]+)'
    arguments = re.findall(arg_pattern, argument_list)
    
    return arguments

def filter_and_compare_eq(eqs:set[str]):
    """
    Filters a set of strings to check if they match the patterns:
    - eq("{x}","{y}",{number})
    - eq("{x}","{y}")
    For each matching string, compares x and y. If x and y are not the same, 
    stores the string in a new set.

    Args:
        strings_set (set): Set of strings to check.

    Returns:
        set: A new set containing strings that passed the check.
    """
    # Define regex patterns for eq("{x}","{y}",{number}) and eq("{x}","{y}")
    pattern_with_number = r'^eq\("([^"]+)","([^"]+)",\d+\)$'
    pattern_without_number = r'^eq\("([^"]+)","([^"]+)"\)$'
    
    # Initialize the new set to store strings that pass the check
    result_set = set()
    
    for string in eqs:
        # Check for a match with either pattern
        match_with_number = re.match(pattern_with_number, string)
        match_without_number = re.match(pattern_without_number, string)
        
        if match_with_number:
            # Extract x and y from the match
            x, y = match_with_number.groups()
        elif match_without_number:
            # Extract x and y from the match
            x, y = match_without_number.groups()
        else:
            # Skip strings that don't match either pattern
            continue
        
        # Compare x and y, add to the result set if they are not the same
        if x != y:
            result_set.add(string)
    
    return result_set

def get_block_constraint(eqs: set[str]) -> str:
    body = ','.join(eqs)+'.'
    block_constraint = f'{IMPLY} {body}'
    return block_constraint

def get_block_constraints(eqs: set[str]) -> list[str]:
    return [f'{IMPLY} {e}.' for e in eqs ]
    
def get_heur_statements(is_global:bool=True, is_ter:bool=False, is_labelled:bool=False, is_neq:bool = False, is_weight:bool = False)->str:
    global_vars = ['X','Y']
    local_vars = ['T1','I1','T2','I2']
    ter_var = 'R'
    lbl_var = 'I'
    weight = '1'
    sign = 'true' if not is_neq else 'false'
    g_pred = EQO_PRED
    l_pred = EQV_PRED
    if is_weight:
        g_pred = 'w'
        l_pred = 'w'
    elif is_neq:
        g_pred = NEQO_PRED
        l_pred = NEQV_PRED
    
    if is_ter:
        global_vars.append(ter_var)
    if is_labelled:
        global_vars.append(lbl_var)
        local_vars.append(lbl_var)
    if is_weight:
        global_vars.append(weight)
        local_vars.append(weight)
    global_atom = utils.get_atom(g_pred,tuple(global_vars))
    local_atom = utils.get_atom(l_pred,tuple(local_vars))
    heur_g = f'#heuristic {global_atom}. [1,{sign}]'
    heur_l = f'#heuristic {local_atom}. [1,{sign}]'
    heur = heur_g if is_global else heur_l
    return heur


def get_optim_statements(is_global:bool=True, is_ter:bool=False, is_labelled:bool=False, is_max = True, is_weight:bool=False, is_neq = False)->str:
    global_vars = ['X','Y']
    local_vars = ['T1','I1','T2','I2']
    ter_var = 'R'
    lbl_var = 'I'
    optim = 'maximize' if is_max else 'minimize'
    weight = '1@1' if not is_weight else 'W@1'
    g_pred = EQO_PRED
    l_pred = EQV_PRED
    if is_weight:
        g_pred = 'w'
        l_pred = 'w'
    elif is_neq:
        g_pred = NEQO_PRED
        l_pred = NEQV_PRED
    
    if is_ter:
        global_vars.append(ter_var)
    if is_labelled:
        global_vars.append(lbl_var)
        local_vars.append(lbl_var)
    if is_weight:
        global_vars.append('W')
        local_vars.append('W')

    global_atom = utils.get_atom(g_pred,tuple(global_vars))
    local_atom = utils.get_atom(l_pred,tuple(local_vars))
    g_count_vars = global_vars if not is_weight else global_vars[:-1]
    l_count_vars = local_vars if not is_weight else local_vars[:-1]
    g_count_vars = ','.join(g_count_vars)
    l_count_vars = ','.join(l_count_vars)
    
    g_statement = f'#{optim}{{{weight},{g_count_vars}:{global_atom}}}.'
    l_statement = f'#{optim}{{{weight},{l_count_vars}:{local_atom}}}.'
    statement = g_statement if is_global else l_statement
    return statement


if __name__ == "__main__":
    # Example usage:
    rule_example_ungrounded = "not body_literal1(X,Y), body_literal2(Y,Y), X!=Y."
    # mergeo, mergev = get_merge_attributes_local('./experiment/5-uni/music/music-plus.lp')
    #[print(k,v) for k,v in mergeo.items()]
    # [print(k,v) for k,v in mergev.items()]
    body = 'name_basics(TU1), name_basics(TU2),  att(TU1,primaryName,PN),att(TU2,primaryName,PN), att(TU1,primaryProfession,PP),att(TU2,primaryProfession,PP),  att(TU1,nconst,X), att(TU2,nconst,Y), not empty(PN), not empty(PP)'
    print(locate_trc_body_var('X',body))
  #print('eq(X,Y),release(A,B,C).'.replace(EQ_AC_AT_PAT,''))