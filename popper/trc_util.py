from . util import  Literal, format_rule
from typing import Tuple, Set, FrozenSet, List
from itertools import combinations, product


Rule = Tuple[Literal, FrozenSet[Literal]]
Comparison = Tuple[int, str, int, str, int]

def is_relational_atom(lit: Literal) -> bool:
    """
    Relational atom:
    - predicate != 'att' and != 'sim'
    - unary argument denoting tuple variable
    """
    return lit.predicate not in {"att", "sim"} and len(lit.arguments) == 1


def is_attribute_atom(lit: Literal) -> bool:
    """
    Attribute atom:
    att(tid, attr_name, var)
    """
    return lit.predicate == "att" and len(lit.arguments) == 3


def is_similarity_atom(lit: Literal) -> bool:
    """
    Similarity atom:
    sim(var1, var2)
    """
    return lit.predicate == "sim" and len(lit.arguments) == 2


def rel(rule: Rule) -> Set[Literal]:
    """rel(r): all relational atoms in the body"""
    _, body = rule
    return {lit for lit in body if is_relational_atom(lit)}


def comp(rule: Rule) -> Set[Comparison]:
    _, body = rule

    # Collect attribute atoms
    attrs = [
        lit for lit in body
        if is_attribute_atom(lit)
    ]

    comparisons: Set[Comparison] = set()

    # --------
    # Joins (type = 0)
    # --------
    for a1, a2 in combinations(attrs, 2):
        t1, att1, v1 = a1.arguments
        t2, att2, v2 = a2.arguments

        if v1 == v2 and (t1 != t2 or att1 != att2):
            key = tuple(sorted(
                [(t1, att1), (t2, att2)],
                key=lambda x: (x[0], x[1])
            ))
            comparisons.add((key[0][0], key[0][1],
                             key[1][0], key[1][1], 0))

    # --------
    # Similarity (type = 1)
    # --------
    sim_atoms = [lit for lit in body if is_similarity_atom(lit)]

    for sim in sim_atoms:
        v1, v2 = sim.arguments

        A1 = [a for a in attrs if a.arguments[2] == v1]
        A2 = [a for a in attrs if a.arguments[2] == v2]

        for a1 in A1:
            for a2 in A2:
                t1, att1, _ = a1.arguments
                t2, att2, _ = a2.arguments

                key = tuple(sorted(
                    [(t1, att1), (t2, att2)],
                    key=lambda x: (x[0], x[1])
                ))
                comparisons.add((key[0][0], key[0][1],
                                 key[1][0], key[1][1], 1))

    return comparisons


def tuple_vars_of_comparison(c: Comparison) -> Set[int]:
    t1, _, t2, _, _ = c
    return {t1, t2}


def tuple_vars_of_literal(lit: Literal) -> Set[int]:
    """
    var(a) in the paper: tuple variables only
    - relational atom: its single argument
    - attribute atom: first argument (tid)
    """
    if is_relational_atom(lit):
        return {lit.arguments[0]}
    if is_attribute_atom(lit):
        return {lit.arguments[0]}
    return set()


def same_relation(a: Literal, a_prime: Literal) -> bool:
    """Check whether two relational atoms have the same predicate"""
    return a.predicate == a_prime.predicate


def same_comparison(c1: Comparison, c2: Comparison) -> bool:
    _, att1a, _, att1b, type1 = c1
    _, att2a, _, att2b, type2 = c2

    if type1 != type2:
        return False

    return {att1a, att1b} == {att2a, att2b}



def all_pairings(r1: Rule, r2: Rule):
    A = {
        (a, a_prime)
        for a in rel(r1)
        for a_prime in rel(r2)
        if same_relation(a, a_prime)
    }

    C = set()

    comp1 = comp(r1)
    comp2 = comp(r2)

    for (a, a_prime) in A:
        vars_a = tuple_vars_of_literal(a)
        vars_a_prime = tuple_vars_of_literal(a_prime)

        C1 = {
            c for c in comp1
            if vars_a.issubset(tuple_vars_of_comparison(c))
        }

        C2 = {
            c for c in comp2
            if vars_a_prime.issubset(tuple_vars_of_comparison(c))
        }

        for c in C1:
            for c_prime in C2:
                if same_comparison(c, c_prime):
                    C.add((c, c_prime))

    return A, C

# create lists of mapping dict from (tuple) var(c1) to var(c2)
def get_total_mappings(s1,s2):
    set1_list = list(s1)
    set2_list = list(s2)
    for values in product(set2_list, repeat=len(set1_list)):
        yield dict(zip(set1_list, values))
        
def apply_mapping(c1,mapping,max_filling_vars=100, head_vars:tuple[int,int] = None)->tuple[tuple,set]:
    # max_vars = MAX_VARS if max_vars == None else max_vars
    new_c1 = set()
    for lit1 in c1:
        if lit1.predicate == 'att':
            # map argument 0
            tup_var1_mapping = mapping[lit1.arguments[0]]
            # if not head attributes
            # create fresh variables on the 3 position of an attribute literal (in case variable clashing after applying mapping)
            mark = '*' if not head_vars or lit1.arguments[2] != head_vars[0] and lit1.arguments[2] != head_vars[1] else ''
            new_lit1_args = (tup_var1_mapping,lit1.arguments[1], f'{str(lit1.arguments[2])}{mark}')
            new_c1.add((lit1.predicate,new_lit1_args))
        elif lit1.predicate == 'sim':
            mark1 = '*' if not head_vars or lit1.arguments[0] != head_vars[0] and lit1.arguments[0] != head_vars[1] else ''
            mark2 = '*' if not head_vars or lit1.arguments[1] != head_vars[0] and lit1.arguments[1] != head_vars[1] else ''
            new_lit1_args = (f'{str(lit1.arguments[0])}{mark1}', f'{str(lit1.arguments[1])}{mark2}')
            new_c1.add((lit1.predicate,new_lit1_args))
        # for tuple range atom
        else:
            tup_var1_mapping = mapping[lit1.arguments[0]]
            new_lit1_args = tuple([tup_var1_mapping])
            new_c1.add((lit1.predicate,new_lit1_args))
                
    new_c1 = list(new_c1)
    # find variables that do not appear in new_c1 from all possible variables
    all_vars = set(range(0,max_filling_vars))
    new_c1_vars = set()
    to_replace_vars = set()
    for i, (pred,args) in enumerate(new_c1.copy()):
        if pred == 'att':
            new_c1_vars.add(args[0])
            if not args[2].endswith('*'):
                new_c1_vars.add(int(args[2]))
                new_c1[i] = (pred,(args[0],args[1],int(args[2])))
            else:
                # pass if the position already exists before mapping
                # already_exist = [ _args[2] for _p,_args in new_c1 if _p =='att' and _args[0] == args[0] and _args[1] == args[1] and not _args[2].endswith("*") ]
                # if already_exist:
                #     # new_c1[i] = (pred,(args[0],args[1],int(already_exist[0])))
                #     continue
                # else:
                to_replace_vars.add(args[2])
    # get variable names that are not yet used in new c1, ascending order
    # print(new_c1_vars)
    not_yet_taken = sorted(list(all_vars.difference(new_c1_vars)))
    # print(not_yet_taken)
    to_replace_vars_index = dict()
    
    for i,v in enumerate(to_replace_vars):
        #print(i,to_replace_vars,not_yet_taken)

        to_replace_vars_index[v] = not_yet_taken[i]
    # print(to_replace_vars_index)
    # print(new_c1)
    # update new c1 again
    for i, (pred,args) in enumerate(new_c1.copy()):
        _args = list(args)
        for j, arg in enumerate(args):
            if arg in to_replace_vars:
                _args[j] = to_replace_vars_index[arg]
        new_c1[i] = (pred,tuple(_args))
    
    new_c1 = set(new_c1)
    # print(new_c1)
    for lit1, lit2 in combinations(new_c1.copy(),2):
        pred1, args1 = lit1
        pred2, args2 = lit2
        if pred1 == pred2 == 'att' and args1[0] == args2[0] and args1[1] == args2[1] and args1[2] != args2[2]:
            
            if args1[2] < args2[2]:
                if head_vars and args1[2] == head_vars[0]:
                    head_vars = (args2[2],head_vars[1])
                if head_vars and args1[2] == head_vars[1]:
                    head_vars = (head_vars[0],args2[2])
                new_c1.remove((pred1,args1))
            else:
                if head_vars and args2[2] == head_vars[0]:
                    head_vars = (args1[2],head_vars[1])
                if head_vars and args2[2] == head_vars[1]:
                    head_vars = (head_vars[0],args1[2])
                new_c1.remove((pred2,args2))
           
    return head_vars, frozenset(
        Literal(pred, args) if not isinstance(pred, Literal) else pred
        for pred, args in new_c1)

def valid_tuple_mapping(mapping: dict, from_rels: set, to_rels: set) -> bool:
    """
    Check whether a tuple-variable mapping is valid w.r.t. relational atoms.

    mapping: dict[int, int]   (from_tid -> to_tid)
    from_rels: set[Literal]   relational atoms (unary)
    to_rels: set[Literal]     relational atoms (unary)
    """

    # Build lookup tables: tid -> predicate
    from_tid_to_pred = {}
    for lit in from_rels:
        if lit.predicate in {"att", "sim"}:
            continue
        if len(lit.arguments) == 1:
            from_tid_to_pred[lit.arguments[0]] = lit.predicate

    to_tid_to_pred = {}
    for lit in to_rels:
        if lit.predicate in {"att", "sim"}:
            continue
        if len(lit.arguments) == 1:
            to_tid_to_pred[lit.arguments[0]] = lit.predicate

    # Validate mapping
    for from_tid, to_tid in mapping.items():
        if from_tid not in from_tid_to_pred:
            return False
        if to_tid not in to_tid_to_pred:
            return False
        if from_tid_to_pred[from_tid] != to_tid_to_pred[to_tid]:
            return False

    return True
        
def containment_check(c1h:set,c2:set)-> bool:
    c1h_tups = {(lit.predicate,(lit.arguments)) for lit in c1h}
    c2_tups = {(lit.predicate,(lit.arguments)) for lit in c2}
    c2_joins = set()
    for tup, _tup in combinations(c2_tups, 2):
        if tup[0] == 'att' and _tup[0] == 'att' and tup != _tup:
            if tup[1][2] == _tup[1][2]:
                c2_joins.add((tup[1][:-1],_tup[1][:-1]))
    
    # check set containment first
    # issubset means subseteq
    if c1h_tups.issubset(c2_tups):
        # TO REMOVE
        print(f'**** subset subsume')
        print(f'    **** c1h:',c1h_tups)
        print(f'    **** c2:',c2_tups)
        return True
    # otherwise, check attribute joins containment
    else:
        # for every pair of att(tid1,att1,v) att(tid2,att2,v) in c1h, there exist a pair in c2
        included_flag = True
        for tup1 in c1h_tups:
            for tup2 in c1h_tups:
                if tup1[0] == 'att' and tup2[0] == 'att' and tup1[1][:-1] != tup2[1][:-1]:
                    var1 = tup1[1][2]
                    var2 = tup2[1][2]
                    if var1 == var2:
                        included_flag = (tup1[1][:-1],tup2[1][:-1]) in c2_joins or (tup2[1][:-1],tup1[1][:-1]) in c2_joins
                        if not included_flag: return False

        # if there is a pair of attribute joins in c1h not in c2, it c1 \not subsumes c2
        # TO REMOVE
        print(f'**** join check')
        print(f'    **** c2 includes c1h:',included_flag)
        # check similarity containment [skipped] -  if sim containment holds c1h is already a subset of c2
        # check on the same pair of tuples attribute join implications on similarity
        # Note that joins in the same equivalence class have the same variable, so sim-atoms certainly hold variables from different equiv classes.
        # Therefore, no sim-atom is implied by any joins in the same rule bodies
        for tup1 in c1h_tups:
            if tup1[0] == 'sim':
                # a variable occurs in sim-atoms may in different att atoms
                # here look at for the cross product of att-atoms associating to the pair of sim variables in c1h
                # if there exist a pair that make a join in c2
                sim_var1 = tup1[1][0]
                sim_var2 = tup1[1][1]
                sim_var_range = {sim_var1:[],sim_var2:[]}
                for tup2 in c1h_tups:
                    if tup2[0] == 'att':
                        if tup2[1][2] == sim_var1:
                            sim_var_range[sim_var1].append(tuple(tup2[1][:-1]))
                        elif tup2[1][2] == sim_var2:
                                sim_var_range[sim_var2].append(tuple(tup2[1][:-1]))
                pairs  = product(sim_var_range[sim_var1],sim_var_range[sim_var2])
                included_flag = any(((p[0],p[1]) in c2_joins or (p[1],p[0]) in c2_joins) for p in pairs)
                # TO REMOVE
                print(f'**** sim containment check')
                print(f'    **** c2 includes c1h:', included_flag)
                #if not any(((p[0],p[1]) in c2_joins or (p[1],p[0]) in c2_joins) for p in pairs):
                if not included_flag:
                    included_flag = False
                    break
        if not included_flag:
            return False
        else:
            # TO REMOVE
            print(f'**** sim containment check survied')
            # survived all the checks return true
            return included_flag


def atoms_subsume(c1:set,c2:set)->bool:   
    c1_vars = set(lit.arguments[0] for lit in c1 if  is_relational_atom(lit))
    # print(c1_vars)
    c2_vars = set(lit.arguments[0] for lit in c2 if  is_relational_atom(lit))
    print('**** c1 vars1:',c1_vars)
    print('**** c2 vars2:',c2_vars)
    all_mappings = get_total_mappings(c1_vars,c2_vars)
        # TO REMOVE
    for mapping in all_mappings:
        if not valid_tuple_mapping(mapping=mapping,from_rels=c1,to_rels=c2): 
            continue
        print('**** apply mapping:',mapping)
        # applying a mapping from var(c1) to var(c2)
        _,c1h = apply_mapping(c1,mapping)
        print("checking containment c1h:", format_rule((None,c1h)))
        print("checking containment c2:", format_rule((None,c2)))
        if containment_check(c1h,c2):
            return True
    return False

def get_range_pairs(r):
    """
    Returns:
      set of ((rel_pred1, att_name1), (rel_pred2, att_name2))
    """
    head, body = r

    if head is None:
        return set()

    # head variables (e.g. {0,1})
    head_vars = set(head.arguments)

    # map tid -> relational predicate
    tid_to_rel = {}
    for lit in body:
        if is_relational_atom(lit):
            tid_to_rel[lit.arguments[0]] = lit.predicate

    # map head_var -> list of (rel_pred, att_name)
    var_ranges = {v: [] for v in head_vars}

    for lit in body:
        if lit.predicate == 'att':
            tid, att_name, var = lit.arguments
            if var in head_vars and tid in tid_to_rel:
                var_ranges[var].append((tid_to_rel[tid], att_name))

    result = set()

    # pair up head variables
    for v1, v2 in combinations(sorted(head_vars), 2):
        for rp1 in var_ranges.get(v1, []):
            for rp2 in var_ranges.get(v2, []):
                # normalize to avoid symmetry
                pair = tuple(sorted((rp1, rp2)))
                result.add(pair)

    return result


def rule_subsume_trc(r1, r2, range_pair:tuple[tuple[str,str],tuple[str,str]])->bool:
    # r1 subsumes r2 if r1 is a subset of r2
    h1, b1 = r1
    h2, b2 = r2
    # make possible attached-to-head literals combinations for input target in bias
    # first thing after applying mapping is to check resulting head-related atoms match or not
    print('**** rule_subsume_trc:',h1,h2)
    # if rule head not matching or trivial, return false
    if h1 == None or h2 == None:
        return False
    # check whether attached-to-head of both rules matches with range pair
    rel_lits1 = rel(r1)
    rel_lits2 = rel(r2)
    range_pairs_1 = get_range_pairs(r1)
    range_pairs_2 = get_range_pairs(r2)
    print(range_pairs_1)
    print(range_pairs_2)
    if range_pair not in range_pairs_1.intersection(range_pairs_2):
        print('**** range_pair checking:',False)
        return False
    # get mappings
    tvars1 = {rlit.arguments[0] for rlit in rel_lits1}
    tvars2 = {rlit.arguments[0] for rlit in rel_lits2}
    all_mappings = get_total_mappings(tvars1,tvars2)
    for mapping in all_mappings:
        if not valid_tuple_mapping(mapping=mapping,from_rels=rel_lits1,to_rels=rel_lits2):
            # print('**** skip invalid mapping:',mapping)
            continue
        print('**** applying mapping to r1:',mapping)
        # applying a mapping from var(c1) to var(c2)
        r1h = apply_homomorphism_to_rule(r1,mapping)
        print('     **** original rule r1:',format_rule(r1))
        print('     **** map to rule r2:',format_rule(r2))
        print('     **** resulting rule r1h:',format_rule(r1h))
        range_pair_r1h = get_range_pairs(r1h)
        # check head equivalence
        if range_pair not in range_pair_r1h:
            print('**** head equivalence check failed.')
            continue
        elif not range_pair_r1h.intersection(range_pairs_2):
            print('**** head equivalence check failed.')
            continue
        else:
            _,body_r1h = r1h
            if containment_check(body_r1h,b2):
                return True
    return False
    
    # head_tuple1 = {literal.arguments for literal in b1 if literal.predicate == 'att' and (literal.arguments[-1] == h1.arguments[0] or literal.arguments[-1] == h1.arguments[1])}
    # head_tuple2 = {literal.arguments for literal in b2 if literal.predicate == 'att' and (literal.arguments[-1] == h1.arguments[0] or literal.arguments[-1] == h1.arguments[1])}
    # if len(head_tuple1)!=len(head_tuple2):
    #     return False
    # range_pair_head1 = {(r.predicate,lit_args[1]) for r in rel(r1)  for lit_args in head_tuple1 if r.arguments[0] == lit_args[0]}
    # range_pair_head2 = {(r.predicate,lit_args[1]) for r in rel(r2)  for lit_args in head_tuple2 if r.arguments[0] == lit_args[0]}
    # if range_pair_head1!=range_pair_head2:
    #     return False
    # return containment_check(b1h,b2)



def apply_homomorphism_to_rule(rule, h) -> Rule:
    head, body = rule
    head_vars = tuple(arg for arg in head.arguments)
    head_pred = head.predicate
    head_vars, new_body = apply_mapping(body, h, head_vars=head_vars)
    return (Literal(head_pred, head_vars), frozenset(
        Literal(pred, args) if not isinstance(pred, Literal) else pred
        for pred, args in new_body
    ))
    
def remove_comparison_from_body(c, body):
    """
    Remove a comparison c from body without destroying other joins.
    Returns (new_body, new_max_vars).
    """
    t1, att1, t2, att2, typ = c
    body = set(body)

    if typ == 1:
        # similarity: remove sim literals witnessing this comparison
        to_remove = {lit for lit in body if lit.predicate == 'sim'}
        return body - to_remove

    # join: break only the targeted join by freshening ONE side
    # choose (t2, att2) deterministically
    new_body = set()
    for lit in body:
        if lit.predicate == 'att':
            tid, att, v = lit.arguments
            if tid == t2 and att == att2:
                # cancel join by making fresh copy of attribute value variable
                new_body.add(Literal('att', (tid, att, f'{str(v)}*')))
            else:
                new_body.add(lit)
        else:
            new_body.add(lit)

    return new_body

def cleanup_body(body):
    body = set(body)

    # attribute atoms participating in comparisons
    comps = comp((None, body))
    att_pairs = set()
    for t1, a1, t2, a2, _ in comps:
        att_pairs.add((t1, a1))
        att_pairs.add((t2, a2))

    body = {
        lit for lit in body
        if lit.predicate != 'att'
        or (lit.arguments[0], lit.arguments[1]) in att_pairs
    }

    # relational atoms referenced by attribute atoms
    att_tids = {lit.arguments[0] for lit in body if lit.predicate == 'att'}
    body = {
        lit for lit in body
        if not is_relational_atom(lit)
        or lit.arguments[0] in att_tids
    }
    return body


def compute_core(rule,range_pair:tuple[tuple[str,str],tuple[str,str]])->Rule:
    """
    Algorithm 2 COMPUTECORE
    """
    head, body = rule
    # Line 3
    r_prime = rule
    all_tids = {lit.arguments[0] for lit in body if is_relational_atom(lit)} # relational atoms

    # Line 4
    # Initialize h as identity mapping
    h = {tid: tid for tid in all_tids}
    
    # Lines 5–15: fixed point on h
    while True:
        changed = False
        A, C = all_pairings(r_prime, r_prime)
        print("** start with mapping h:",h)
        # print("** parings:",A)
        for (a, a_prime) in A:
            v_from = a_prime.arguments[0]
            v_to  = a.arguments[0]

            if v_from == v_to:
                continue

            h_prime = h.copy()
            h_prime[v_from] = v_to
            print("** adding another variable mapping h':", h_prime)
            print("** before mapping r'",format_rule(r_prime))
            r_h = apply_homomorphism_to_rule(r_prime, h_prime)
            print("** apply h' to r obtained:",format_rule(r_h))
            if rule_subsume_trc(r_prime, r_h,range_pair=range_pair):
                h = h_prime
                r_prime = r_h
                changed = True
                break   # line 12

        if not changed:
            break       # line 15

    # Lines 16–20: comparison minimisation
    head, body = r_prime
    body = set(body)

    for c in list(comp(r_prime)):
        # remove comparison c
        new_body = remove_comparison_from_body(c, body)

        # IMPORTANT: cleanup immediately
        cleaned_body = cleanup_body(new_body)

        # now check subsumption against the cleaned body
        if atoms_subsume(
            body,
            cleaned_body
        ):
            body = cleaned_body

    # Line 21
    return (head, frozenset(body))

def test_all_pairing():
    # ---------- Rule r1 ----------
    r1_head = Literal(predicate="eqo", arguments=(0, 1))
    r1_body = frozenset({
        Literal(predicate="movie", arguments=(2,)),
        Literal(predicate="movie", arguments=(3,)),
        Literal(predicate="att", arguments=(2, "mid", 0)),
        Literal(predicate="att", arguments=(3, "mid", 1)),
        Literal(predicate="att", arguments=(2, "cid", 4)),
        Literal(predicate="att", arguments=(3, "cid", 4)),
        Literal(predicate="att", arguments=(3, "title", 5)),
        Literal(predicate="att", arguments=(2, "title", 6)),
        Literal(predicate="sim", arguments=(5, 6)),
    })
    r1 = (r1_head, r1_body)

    # ---------- Rule r2 ----------
    r2 = (r1_head, r1_body)
    
    # r2_head = Literal(predicate="eqo", arguments=(0, 1))
    # r2_body = frozenset({
    #     Literal(predicate="movie", arguments=(2,)),
    #     Literal(predicate="movie", arguments=(3,)),
    #     Literal(predicate="att", arguments=(2, "mid", 1)),
    #     Literal(predicate="att", arguments=(3, "mid", 0)),
    #     Literal(predicate="att", arguments=(2, "cid", 4)),
    #     Literal(predicate="att", arguments=(3, "cid", 4)),
    #     Literal(predicate="att", arguments=(3, "rid", 7)),
    #     Literal(predicate="att", arguments=(2, "title", 5)),
    #     Literal(predicate="att", arguments=(3, "title", 6)),
    #     Literal(predicate="sim", arguments=(6, 5)),
    # })
    #r2 = (r2_head, r2_body)

    # ---------- Run ALLPAIRINGS ----------
    A, C = all_pairings(r1, r2)
    print(C)
    # ---------- Pretty printing ----------
    print("\n=== Relational pairings A ===")
    for a, a_prime in A:
        print(f"  ({a.predicate}{a.arguments}, {a_prime.predicate}{a_prime.arguments})")

    print("\n=== Comparison pairings C ===")
    for c1, c2 in C:
        def fmt(c):
            t1, att1, t2, att2, typ = c
            kind = "JOIN" if typ == 0 else "SIM"
            return f"{kind}: ({t1}.{att1}, {t2}.{att2})"

        print(f"  {fmt(c1)}  <->  {fmt(c2)}")



def test_compute_core():
    """
    Test the compute_core function on a sample ER rule.
    """

    # --- Sample literals ---
    
    # attribute atoms
    att_2_mid = Literal("att", (2, "mid", 0))
    att_3_mid = Literal("att", (3, "mid", 1))
    att_2_title = Literal("att", (2, "title", 4))
    att_3_title = Literal("att", (3, "title", 4))
    att_2_rid = Literal("att", (2, "rid", 5))
    att_3_rid = Literal("att", (3, "rid", 5))  # join on rid
    att_6_title = Literal("att", (6, "title", 4))

    # similarity atom
    sim_4_4 = Literal("sim", (4, 4))  # similarity between mid variables

    # relational atoms
    rel_2 = Literal("movie", (2,))
    rel_3 = Literal("movie", (3,))
    rel_6 = Literal("movie", (6,))

    # head
    head = Literal("eqo", (0, 1))

    # body with attributes, relations, and similarity
    body = frozenset({
        att_2_mid,
        att_3_mid,
        att_2_title,
        att_3_title,
        att_2_rid,
        att_3_rid,
        sim_4_4,
        rel_2,
        rel_3,
        att_6_title,
        rel_6
    })

    # input rule
    rule = (head, body)
    # expected range pair
    range_pair = (('movie', 'mid'), ('movie', 'mid'))
    # --- Run compute_core ---
    core_rule = compute_core(rule,range_pair)

    # --- Output results ---
    print("Original rule:")
    print(format_rule(rule))


    print("\nComputed core:")
    print(format_rule(core_rule))
    # --- Assertions / checks ---
    core_body_predicates = {lit.predicate for lit in core_rule[1]}
    
    assert "movie" in core_body_predicates, "Relational atoms with attributes should remain"
    assert "att" in core_body_predicates, "Attribute atoms participating in comparisons should remain"
    assert "sim" in core_body_predicates, "Similarity atom should remain if still relevant"

    print("\nTest passed: core computed and cleaned correctly.")
    
    
def test_rule_subsume_trc_positive():
    # head
    h1 = Literal('eqo', (0, 1))
    h2 = Literal('eqo', (0, 1))

    # r1 body (more specific)
    b1 = {
        Literal('movie', (2,)),
        Literal('movie', (3,)),
        Literal('att', (2, 'mid', 0)),
        Literal('att', (3, 'mid', 1)),
        Literal('att', (2, 'rid', 4)),
        Literal('att', (3, 'rid', 4)),
        Literal('cast', (5,)),
        Literal('cast', (6,)),
        Literal('att', (2, 'cid', 7)),
        Literal('att', (3, 'cid', 8)),
        Literal('att', (5, 'cid', 7)),
        Literal('att', (6, 'cid', 8)),
        Literal('att', (5, 'name', 9)),
        Literal('att', (6, 'name', 10)),
        Literal('sim', (9,10)),
        # join on rid
    }

    # r2 body (more general)
    b2 = {
        Literal('movie', (5,)),
        Literal('movie', (6,)),
        Literal('att', (5, 'mid', 0)),
        Literal('att', (6, 'mid', 1)),
        Literal('att', (5, 'rid', 4)),
        Literal('att', (6, 'rid', 4)),
    }
    
    b3 = {
        Literal('movie', (2,)),
        Literal('movie', (3,)),
        Literal('att', (2, 'mid', 0)),
        Literal('att', (3, 'mid', 1)),
        Literal('att', (2, 'rid', 4)),
        Literal('att', (3, 'rid', 5)),
        Literal('sim', (4,5)),
        # join on rid
    }
    
    
    b4 = {
        Literal('movie', (2,)),
        Literal('movie', (3,)),
        Literal('att', (2, 'mid', 7)),
        Literal('att', (3, 'mid', 8)),
        Literal('att', (2, 'rid', 4)),
        Literal('att', (3, 'rid', 4)),
        Literal('sim', (4,4)),
        Literal('cast', (5,)),
        Literal('cast', (6,)),
        Literal('att', (2, 'cid', 0)),
        Literal('att', (3, 'cid', 1)),
        Literal('att', (5, 'cid', 0)),
        Literal('att', (6, 'cid', 1)),
        Literal('att', (5, 'name', 9)),
        Literal('att', (6, 'name', 9)),
        # join on rid
    }


    b5 = {
        Literal('movie', (2,)),
        Literal('movie', (3,)),
        Literal('att', (2, 'mid', 7)),
        Literal('att', (3, 'mid', 8)),
        Literal('cast', (5,)),
        Literal('cast', (6,)),
        Literal('att', (2, 'rid', 4)),
        Literal('att', (3, 'rid', 11)),
        Literal('sim', (4,11)),
        Literal('att', (2, 'cid', 0)),
        Literal('att', (3, 'cid', 1)),
        Literal('att', (5, 'cid', 0)),
        Literal('att', (6, 'cid', 1)),
        Literal('att', (5, 'name', 9)),
        Literal('att', (6, 'name', 10)),
        Literal('sim', (9,10)),
        # join on rid
    }

    r1 = (h1, b1)
    r2 = (h2, b2)
    r3 = (h1,b3)
    r4 = (h1,b4)
    r5 = (h1,b5)

    # expected range pair
    range_pair = (('cast', 'cid'), ('cast', 'cid'))

    result = rule_subsume_trc(r5, r4, range_pair)

    assert result is True, "Expected r2 to subsume r1 under the given range pair"
    print("✅ test_rule_subsume_trc_positive passed")
    


def test_atom_subsumes_positive():
    # head
    h1 = Literal('eqo', (0, 1))
    h2 = Literal('eqo', (0, 1))

    # r1 body (more specific)
    b1 = {
        Literal('movie', (2,)),
        Literal('movie', (3,)),
        Literal('att', (2, 'mid', 0)),
        Literal('att', (3, 'mid', 1)),
        Literal('att', (2, 'rid', 4)),
        Literal('att', (3, 'rid', 4)),
        Literal('cast', (5,)),
        Literal('cast', (6,)),
        Literal('att', (2, 'cid', 7)),
        Literal('att', (3, 'cid', 8)),
        Literal('att', (5, 'cid', 7)),
        Literal('att', (6, 'cid', 8)),
        Literal('att', (5, 'name', 9)),
        Literal('att', (6, 'name', 10)),
        Literal('sim', (9,10)),
        # join on rid
    }

    # r2 body (more general)
    b2 = {
        Literal('movie', (5,)),
        Literal('movie', (6,)),
        Literal('att', (5, 'mid', 0)),
        Literal('att', (6, 'mid', 1)),
        Literal('att', (5, 'rid', 4)),
        Literal('att', (6, 'rid', 4)),
    }
    
    b3 = {
        Literal('movie', (2,)),
        Literal('movie', (3,)),
        Literal('att', (2, 'mid', 0)),
        Literal('att', (3, 'mid', 1)),
        Literal('att', (2, 'rid', 4)),
        Literal('att', (3, 'rid', 5)),
        Literal('sim', (4,5)),
        # join on rid
    }
    
    
    b4 = {
        Literal('movie', (2,)),
        Literal('movie', (3,)),
        Literal('att', (2, 'mid', 7)),
        Literal('att', (3, 'mid', 8)),
        Literal('att', (2, 'rid', 4)),
        Literal('att', (3, 'rid', 4)),
        Literal('sim', (4,4)),
        Literal('cast', (5,)),
        Literal('cast', (6,)),
        Literal('att', (2, 'cid', 0)),
        Literal('att', (3, 'cid', 1)),
        Literal('att', (5, 'cid', 0)),
        Literal('att', (6, 'cid', 1)),
        Literal('att', (5, 'name', 9)),
        Literal('att', (6, 'name', 9)),
        # join on rid
    }


    b5 = {
        Literal('movie', (2,)),
        Literal('movie', (3,)),
        Literal('att', (2, 'mid', 7)),
        Literal('att', (3, 'mid', 8)),
        Literal('cast', (5,)),
        Literal('cast', (6,)),
        Literal('att', (2, 'rid', 4)),
        Literal('att', (3, 'rid', 11)),
        Literal('sim', (4,11)),
        Literal('att', (2, 'cid', 0)),
        Literal('att', (3, 'cid', 1)),
        Literal('att', (5, 'cid', 0)),
        Literal('att', (6, 'cid', 1)),
        Literal('att', (5, 'name', 9)),
        Literal('att', (6, 'name', 10)),
        Literal('sim', (9,10)),
        # join on rid
    }

    r1 = (h1, b1)
    r2 = (h2, b2)
    r3 = (h1,b3)
    r4 = (h1,b4)
    r5 = (h1,b5)

    # expected range pair
    range_pair = (('cast', 'cid'), ('cast', 'cid'))

    result = atoms_subsume(b4, b5)

    assert result is True, "Expected r2 to subsume r1 under the given range pair"
    print("✅ test_rule_subsume_trc_positive passed")
    