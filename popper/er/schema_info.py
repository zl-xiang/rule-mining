import er_util as utils
from trans_utils import get_attr_types
# from mpi import MPIWrapper


DISTINCT = 0
PARTIAL = 1

VAL_DOMAIN = 'v'
OBJ_DOMAIN = 'o'
RELATION = 'rel'


STRING = 'string'
NUMBER = 'number'
TIME = 'time_stamp'

SEP_COMMA = ','
SEP_AND = ' and '
SEP_AMP = ' & '

SEP_LST = [SEP_COMMA,SEP_AMP,SEP_AND] 

DF_EMPTY = "nan"

# predicate name
SIM_PRED = 'sim'
ACTIVE_DOM = 'adom'
EQ_PRED = 'eq'
ANONYM_VAL = '_'
TUPLE_PRED = 't'
CONST_PRED = 'c'



## stats
REL_NUM ="#rel"
ATTR_NUM ="#attr"
EMPTY_RATIO = "empty_ratio"
DISTINCT_VAL = "distinct_val"
REF_NUM = "#ref"
REC_NUM = "#record"
TOTAL_REC = '#total_records'
TOTAL_CONSTANT = '#total_constants'
TOTAL_ATTR = '#total_attr'
DUP_NUM = '#ground_truth'


LACE = 0
LACE_P = 1
VLOG_LB = 2
VLOG_UB = 3


class Attribute:
    # categorical values
    CAT = 'cat'
    # sequence of categorical values
    CAT_SEQ = 'cat_seq'
    # numeric values
    NUM = 'numeric'
    # numeric sequence
    NUM_SEQ = 'numeric_seq'
    # date
    DATE = 'date'
    # string values
    STR = 'string'
    # numeric sequence
    STR_SEQ = 'string_seq'
    # ids/referenced ids
    IDS = 'id'
    
    DTYPE_LST = [CAT,CAT_SEQ,STR,STR_SEQ,NUM,NUM_SEQ,IDS]
    
    NON_SIM_LST = [CAT,IDS]
    
    # LACE type
    MERGE = 0
    SIM = 1
    
    ##LACE+ type
    TID = 0
    O_MERGE = 2
    V_MERGE = 3
    SINGLETON = 4

    
    def __init__(self, id, name:str, type:int= SIM,data_type:str = STR, is_list:bool = False, rel_name= None) -> None:
        # assert data_type in self.DTYPE_LST
        self.id = id # id will be unique under a schema
        # self.pos = pos
        self.name = name # could be a set of names
        self.type = type
        self.is_list = is_list
        #self.comparable = comparable
        # a list of comparable partially to A attribute of R relation occurring in the same schema
        # self.plist = plist
        # [2023-1-16] adding data type to columns of schema and compute the similarities accordingly
        self.data_type = data_type
        self.rel_name = rel_name
 
        
    def __eq__(self, __o: object) -> bool:
        return __o is not None and __o.id == self.id 
    
    def __ne__(self, __o: object) -> bool:
        return not self.__eq__(__o)
    
    def __hash__(self) -> int:
        return hash(self.id)

    def __str__(self) -> str:
        return f"{{id:{self.id}, name:{self.name}, rel_name:{self.rel_name} type:{self.type}, data_type: {self.data_type}, is_list: {self.is_list}}}"

# will be a set of meta information
class Relation:
    def __init__(self,s_id,id,name,attrs=None, main_idx=0, is_dup = False) -> None:
        self.s_id = s_id
        self.name = name 
        self.id = id
        # sequence of attribute position and the attribute domain of a schema 
        # TODO: write an add function to avoid duplication
        # expected to be ordered, thus we use list here instead
        self.attrs:list[Attribute] = attrs if attrs is not None else list()
        #self.tbl = tbl
        # self.type = type
        self.main_idx = main_idx
        # [2023-01-20] added to distinguish is corrupted or not (if known)
        self.is_dup = is_dup

    def __eq__(self, __o: object) -> bool:
        #if __o is None:
            # return False
        o_keys = set([a for a in __o.attrs])
        self_keys = set([a for a in self.attrs])
        flag = False if o_keys.intersection(self_keys) != self_keys else True
        #False in [__o.attrs[k]==self.attrs[k] for k in self_keys]
        # require r_id and all attributes are the same
        return __o.id == self.id and flag
    
    def __ne__(self, __o: object) -> bool:
        return not self.__eq__(__o)
    
    def __hash__(self) -> int:
        # IMPORTANT: hashing attrs makes the hash value mutable (not static), 
        # thus we hash id only, and leave __eq__ as it be
        # + sum([hash(a[1]) for a in self.attrs])
        return hash(self.id) 
    
    def __str__(self) -> str:
        # print(len(self.attrs))
        return f"{{id:{self.id}, name:{self.name}, attrs: {list(map(str,self.attrs))}}}"
    
    
    def attr_index(self,attr_id:str)->int:
        for i, a in enumerate(self.attrs):
            if a.id == attr_id:
                return i
        

class Schema: 
    PAIRWISE = 0
    MULTREL = 1
    """_summary_
    
    @refs: referential dependencies of the schema, of the shape 
            dictionary {(rel1,ref_attr_1):(rel2,refed_attr_1),...,(rel_n,ref_attr_m),(rel_j,refed_attr_k)},
            circular references are not expected here.
    """
    def __init__(self,  id, name:str='', tbls:dict = None, ground_truth:dict = None, refs:dict = None, spec_dir = str, ver = LACE, is_trc = False) -> None:
        assert id is not None
        self.name = name if len(name)> 0 else f'def_schema_{id}'
        self.id = id
        self.spec_dir = spec_dir
        # id formatted as s_id-r_id
        self.relations:set[Relation] = set()
        self.attrs:set[Attribute] = set()
        self.attrs_lst = list()
        self.attr_num = 0
        self.rel_num = 0
        self.tbls = tbls
        self.ground_truth = ground_truth
        self.refs = refs
        self.ver = ver
        self.is_trc = is_trc
        # global uid
        self.u_id = 0
        mergeo_attrs = dict()
        mergev_attrs = dict()
        for k,v in get_attr_types(spec_dir).items():
            if v == Attribute.O_MERGE:
                if k[0] not in mergeo_attrs:
                    mergeo_attrs[k[0]] = set()
                mergeo_attrs[k[0]].add(k[1])
            elif v == Attribute.V_MERGE:
                if k[0] not in mergev_attrs:
                    mergev_attrs[k[0]] = set()
                mergev_attrs[k[0]].add(k[1])
        # load the set of all attributes
        for k,v in tbls.items():
            tbl = tbls[k]
            k = k[:-2] if k.endswith('_c') else k
            rel = Relation(s_id=self.id,id = self.rel_num, name=k)    
            columns = list(tbl.columns.values) 
            if self.ver == LACE_P and not self.is_trc:
                for i,c in enumerate(columns):
                    attr_type = Attribute.SINGLETON # [2024-4-13] those do not participate any merges
                    if k in mergeo_attrs and i in mergeo_attrs[k]:
                        attr_type = Attribute.O_MERGE
                    elif k in mergev_attrs and i in mergev_attrs[k]:
                        #print(c,'v')
                        attr_type = Attribute.V_MERGE
                    # a_type = Attribute.MERGE if ver == LACE else Attribute.O_MERGE
                    data_type = Attribute.STR if c!='tid' else Attribute.IDS
                    attr = Attribute(id = self.attr_num, name = f'{c}',type=attr_type, \
                        # assumption here is merge attributes are not some kind of textual string
                        data_type= data_type \
                        ,rel_name=k)
                    #print(attr)
                    self.add_attr(attr=attr)
                    rel.attrs.append(attr)
                    # print(rel)
                    self.add_rel(rel=rel)
            # initialise attributes
            elif self.ver == LACE_P and self.is_trc:
                for i,c in enumerate(columns):
                    attr_type = Attribute.SINGLETON # [2024-4-13] those do not participate any merges
                    
                    if k in mergeo_attrs and c in mergeo_attrs[k]:
                        #print(rel.name,mergeo_attrs[k])
                        #print(c,'o')
                        attr_type = Attribute.O_MERGE
                    elif k in mergev_attrs and c in mergev_attrs[k]:
                        #print(c,'v')
                        attr_type = Attribute.V_MERGE
                    # a_type = Attribute.MERGE if ver == LACE else Attribute.O_MERGE
                    data_type = Attribute.STR if i!=0 else Attribute.IDS
                    attr = Attribute(id = self.attr_num, name = f'{c}',type=attr_type, \
                        # assumption here is merge attributes are not some kind of textual string
                        data_type= data_type \
                        ,rel_name=k)
                    #print(attr)
                    self.add_attr(attr=attr)
                    rel.attrs.append(attr)
                    # print(rel)
                    self.add_rel(rel=rel)


        to_be_updated = dict()
        # to be fixed
        # iterate relations, check attributes
        # identify compatible attributes and consider them as one
        for r in self.relations:
            for i,a in enumerate(r.attrs):
                if self.refs != None and (r.name,a.name) in self.refs:
                    #print((r.name,a.name),'--')
                    refed_r_name = self.refs[(r.name,a.name)][0]
                    refed_attr_name = self.refs[(r.name,a.name)][1]
                    refed_r = self.rel_index(refed_r_name) #TODO, replace attr list by string of ids
                    refed_attr = [_a for _a in refed_r.attrs if _a.name == refed_attr_name][0]
                    referring_r = self.rel_index(r.name)
                    referring_attr = [_a for _a in referring_r.attrs if _a.name == a.name][0]
                    for _a in refed_r.attrs:
                        if _a.name == refed_attr_name:
                            if refed_attr.type != referring_attr.type and referring_attr.type == Attribute.O_MERGE:
                                _a.type = Attribute.O_MERGE
                                to_be_updated[(refed_r_name,refed_r.attr_index(refed_attr.id))] = _a
                            to_be_updated[(r.name,i)] = _a
                            break
        # update attributes of relations
        for t,a in to_be_updated.items():
            r = self.rel_index(t[0])
            r.attrs[t[1]] = a
        # create a new attribute list for the schema
        self.attrs = set()
        for r in self.relations:
            #print(r)
            self.attrs.update(set(r.attrs))
        self.attr_num = len(self.attrs)
        # remove redundant attributes
        # update the relations      
                       
    def get_uidx(self,):
        self.u_id += 1
        return str(self.u_id)
    
        
    def add_attr(self,attr):
        if isinstance(attr,set):
            self.attrs.update(attr)
            self.attr_num += len(attr)
        else:
            self.attrs.add(attr)
            self.attrs_lst.append(attr)
            self.attr_num +=1
            
    def add_rel(self,rel):
        if isinstance(rel,set):
            self.relations.update(rel)
            self.rel_num += len(rel)
        else:
            self.relations.add(rel)
            self.rel_num +=1
            

    def attr_index(self,id):
        return self.get_attr_dict()[id]
    
    def index_attr(self,attr_name,rel_name)-> Attribute:
        attr = None
        for a in self.attrs:
            if a.name == attr_name and a.rel_name == rel_name:
                attr = a
                break
        return attr
    
    def attr_index_name(self,name):
        a_dict = self.get_attr_name_dict()
        if name in a_dict: 
            return a_dict[name]
        else: None

    def rel_index(self,r_name) -> Relation:
        rel_dict = {r.name:r for r in self.relations}
        if r_name in rel_dict:
            return rel_dict[r_name]
        else:
            return None
    
    
    def get_attr_dict(self,): 
        return {a.id:a for a in self.attrs}
    
    def get_attr_name_dict(self,): 
        return {a.name:a for a in self.attrs}
    
    def get_rel_dict(self,):
        return {r.id:r for r in self.relations}
    
    def stats (self,) -> dict:
        print("* Processing reocrd stats of the schema ...")
        stats = {'domain_attr':0, REL_NUM:0, TOTAL_REC:0 , TOTAL_CONSTANT:0, TOTAL_ATTR:0, REC_NUM:{}, ATTR_NUM:{},EMPTY_RATIO:{},DISTINCT_VAL:{},REF_NUM:{}}
        stats[REL_NUM] = len(self.tbls.items())
        for r_name,tbl in self.tbls.items():
            # print(tbl[0])
            stats[ATTR_NUM][r_name] = len(tbl.columns)
            stats[TOTAL_ATTR]+= len(tbl.columns)
            stats['domain_attr'] = len(self.attrs)
            stats[REC_NUM][r_name] = len(tbl)
            stats[TOTAL_REC] += len(tbl) 
            # dataframe tolist for value counting
            for col in tbl.columns:
                distinct_cnt = len(tbl[col].value_counts(dropna=True))
                stats[DISTINCT_VAL][r_name+'.'+col] = distinct_cnt
                stats[TOTAL_CONSTANT] += distinct_cnt
            emp_ratio = {c:0 for c in tbl.columns}
            for _, row in tbl.iterrows():
                for col in tbl.columns:
                    v = row[col]
                    if utils.is_empty(v):
                        emp_ratio[col]+=1
            stats[EMPTY_RATIO][r_name] = {k:round(e/stats[REC_NUM][r_name],3) for k,e in emp_ratio.items()}            
        return stats        
    
    def schema_info(self,):
        print(f'Schema Name: {self.name}')
        # [self.schema_log.info('Relation % : %', [r.name,r]) for r in self.relations] 
        sum = 0
        for k,v in self.tbls.items():
            sum+= len(v[1])
            print(f'Relation {k} has {str(len(v[1]))} of tuples.')
        print(f'#Tuples of schema {self.name} is {str(sum)}.')
