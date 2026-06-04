from . util import  Literal, format_rule, is_int
from . trc_util import Rule, is_relational_atom, remove_comparison_from_body, comp, rel, get_range_pairs, valid_tuple_mapping
from . trc_util import is_valid_rule, same_relation, same_comparison, cleanup_body, tuple_vars_of_comparison, tuple_vars_of_literal
from . trc_util import collect_sim_var_pairs, unify_fol_var, normalise_body_var, is_similarity_atom, is_attribute_atom
from itertools import combinations, product,permutations
from collections import defaultdict


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
    seen_mapping = {}
    fixed_mapping = {}
    # Lines 5–15: fixed point on h
    while True:
        changed = False
        A, C = all_pairings(r_prime, r_prime)
        # [print(a[0].predicate, a[0].arguments, a[1].predicate,a[1].arguments) for a in A]
        # print("** start with mapping h:",h)
        # print("** parings:",A)
        for (a, a_prime) in A:
            v_from = a_prime.arguments[0]
            v_to  = a.arguments[0]

            if v_from == v_to:
                #print(f"** skip identity mapping {str(v_from)}-> {str(v_to)}")
                continue
            if v_from in seen_mapping and v_to == seen_mapping[v_from]:
                #print(f"** skip seen mapping {str(v_from)}-> {str(v_to)}")
                continue
            if v_from in fixed_mapping:
                #print(f"** skip already fixed mapping {str(v_from)}-> {str(v_to)}")
                continue
            
            h_prime = h.copy()
            h_prime[v_from] = v_to
            seen_mapping[v_from] = v_to
            #print("** adding another variable mapping h':", h_prime)
            #print("** before mapping r'",format_rule(r_prime))
            r_h = apply_homomorphism_to_rule(rule, h_prime)
            #print("** apply h' to r obtained:",format_rule(r_h))
            if not is_valid_rule(r_h,range_pair):
                #print(f"** skip bad rule after mapping")
                continue
            
            if rule_subsume_trc(r_prime, r_h,range_pair=range_pair):
                fixed_mapping[v_from] = v_to
                h = h_prime
                r_prime = r_h
                changed = True
                break   # line 12

        if not changed:
            #print("** no more suitable mappings")
            break       # line 15

    # Lines 16–20: comparison minimisation
    head, body = r_prime
    body = set(body)
    
    for c in list(comp(r_prime)):
        #print("** Clean up redundant comparisons")
        #print("     ** Before cleaning:", format_rule((None,body)))
        #print("     ** To remove:", c)
        # remove comparison c
        new_body = remove_comparison_from_body(c, body)

        # IMPORTANT: cleanup immediately
        cleaned_body = cleanup_body(new_body)
        #print("     ** After cleaning:", format_rule((None,cleaned_body)))
        # now check subsumption against the cleaned body
        # identity mapping applied
        if containment_check(
            body,
            cleaned_body
        ):
            #print("     ** Valid cleaning")
            body = cleaned_body
        # # TO REMOVE
        # else:
        #     print("     ** Invalid cleaning")

    # Line 21
    return (head, frozenset(body))

def apply_homomorphism_to_rule(rule, h) -> Rule:
    head, body = rule
    head_vars = tuple(arg for arg in head.arguments)
    head_pred = head.predicate
    head_vars, new_body = apply_mapping(body, h, head_vars=head_vars)
    return (Literal(head_pred, head_vars), frozenset(
        Literal(pred, args) if not isinstance(pred, Literal) else pred
        for pred, args in new_body
    ))
    
def rule_subsume_trc(r1, r2, range_pair:tuple[tuple[str,str],tuple[str,str]])->bool:
    # r1 subsumes r2 if r1 is a subset of r2
    h1, b1 = r1
    h2, b2 = r2
    # make possible attached-to-head literals combinations for input target in bias
    # first thing after applying mapping is to check resulting head-related atoms match or not
    # print('**** rule_subsume_trc:',h1,h2)
    # if rule head not matching or trivial, return false
    if h1 == None or h2 == None:
        return False
    # check whether attached-to-head of both rules matches with range pair
    rel_lits1 = rel(r1)
    rel_lits2 = rel(r2)
    range_pairs_1 = get_range_pairs(r1)
    range_pairs_2 = get_range_pairs(r2)
    # print(range_pairs_1)
    # print(range_pairs_2)
    if range_pair not in range_pairs_1.intersection(range_pairs_2):
        # print('**** range_pair checking:',False)
        return False
    # get mappings
    tvars1 = {rlit.arguments[0] for rlit in rel_lits1}
    tvars2 = {rlit.arguments[0] for rlit in rel_lits2}
    all_mappings = get_total_mappings(tvars1,tvars2)
    for mapping in all_mappings:
        if not valid_tuple_mapping(mapping=mapping,from_rels=rel_lits1,to_rels=rel_lits2):
            # print('**** skip invalid mapping:',mapping)
            continue
        # print('**** applying mapping to r1:',mapping)
        # applying a mapping from var(c1) to var(c2)
        r1h = apply_homomorphism_to_rule(r1,mapping)
        # print('     **** original rule r1:',format_rule(r1))
        # print('     **** map to rule r2:',format_rule(r2))
        # print('     **** resulting rule r1h:',format_rule(r1h))
        range_pair_r1h = get_range_pairs(r1h)
        # check head equivalence
        if range_pair not in range_pair_r1h:
            # print('**** head equivalence check failed.')
            continue
        elif not range_pair_r1h.intersection(range_pairs_2):
            # print('**** head equivalence check failed.')
            continue
        else:
            _,body_r1h = r1h
            if containment_check(body_r1h,b2):
                return True
    return False
    
def atoms_subsume(c1:set,c2:set)->bool:   
    c1_vars = set(lit.arguments[0] for lit in c1 if  is_relational_atom(lit))
    # print(c1_vars)
    c2_vars = set(lit.arguments[0] for lit in c2 if  is_relational_atom(lit))
    # print('**** c1 vars1:',c1_vars)
    # print('**** c2 vars2:',c2_vars)
    all_mappings = get_total_mappings(c1_vars,c2_vars)
        # TO REMOVE
    for mapping in all_mappings:
        if not valid_tuple_mapping(mapping=mapping,from_rels=c1,to_rels=c2): 
            continue
        # print('**** apply mapping:',mapping)
        # applying a mapping from var(c1) to var(c2)
        _,c1h = apply_mapping(c1,mapping)
        # print("checking containment c1h:", format_rule((None,c1h)))
        # print("checking containment c2:", format_rule((None,c2)))
        if containment_check(c1h,c2):
            return True
    return False

def containment_check(c1h:set,c2:set)-> bool:
    c1h_tups = {(lit.predicate,(lit.arguments)) for lit in c1h}
    c2_tups = {(lit.predicate,(lit.arguments)) for lit in c2}
    c2_joins = set()
    for tup, _tup in combinations(c2_tups, 2):
        if tup[0] == 'att' and _tup[0] == 'att' and tup != _tup:
            if tup[1][2] == _tup[1][2]:
                c2_joins.add((tup[1][:-1],_tup[1][:-1]))
    c2_sim_joins = set()
    c2_sim_atoms = {lit for lit in c2 if is_similarity_atom(lit)}
    c2_atts = {lit for lit in c2 if is_attribute_atom(lit)}
    for a1,a2 in product(c2_atts,repeat=2):
        for sim in c2_sim_atoms:
            if a1.arguments[-1] == sim.arguments[0] and a2.arguments[-1] == sim.arguments[-1]:
                c2_sim_joins.add((a1.arguments[:-1],a2.arguments[:-1]))
    
    # check set containment first
    # issubset means subseteq
    if c1h_tups.issubset(c2_tups):
        # TO REMOVE
        # print(f'**** subset subsume')
        # print(f'    **** c1h:',c1h_tups)
        # print(f'    **** c2:',c2_tups)
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
        # print(f'**** join check')
        # print(f'    **** c2 includes c1h:',included_flag)
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
                included_flag = any(((p[0],p[1]) in c2_joins or (p[1],p[0]) in c2_joins or (p[0],p[1]) in c2_sim_joins or (p[1],p[0]) in c2_sim_joins) for p in pairs)
                # TO REMOVE
                # print(f'**** sim containment check')
                # print(f'    **** c2 includes c1h:', included_flag)
                #if not any(((p[0],p[1]) in c2_joins or (p[1],p[0]) in c2_joins) for p in pairs):
                if not included_flag:
                    included_flag = False
                    break
        if not included_flag:
            return False
        else:
            # TO REMOVE
            # print(f'**** sim containment check survied')
            # survived all the checks return true
            return included_flag



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
                if (pred1,args1) in new_c1:
                    new_c1.remove((pred1,args1))
            else:
                if head_vars and args2[2] == head_vars[0]:
                    head_vars = (args1[2],head_vars[1])
                if head_vars and args2[2] == head_vars[1]:
                    head_vars = (head_vars[0],args1[2])
                if (pred2,args2) in new_c1:
                    new_c1.remove((pred2,args2))
           
    return head_vars, frozenset(
        Literal(pred, args) if not isinstance(pred, Literal) else pred
        for pred, args in new_c1)
    
    
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
        
        


def get_sim_specs(rule, pairs, max_vars=None):
    """
    Reverse of join–similarity relaxation.

    Performs permutation-based variable unifications
    for sim(v1,v2) pairs.
    """
    # head,body = rule
    # all_bvars = sorted(
    #     {x for lit in body for x in lit.arguments if is_int(x)}
    # )
    if not pairs:
        return set()

    results = set()

    initial_vars = {
        x for lit in rule[1] for x in lit.arguments if is_int(x)
    }

    for perm in permutations(pairs):
        current_rule = rule
        used_vars = set(initial_vars)

        valid = True
        for (v1, v2) in perm:
            if v1 == v2:
                continue

            # unify v2 → v1
            current_rule = unify_fol_var(current_rule, v2, v1)
            used_vars.discard(v2)
            new_b = set()
            # discard redundant sim atoms
            for bl in current_rule[1]:
                if bl.predicate == 'sim' and bl.arguments[0] == bl.arguments[1]:
                    continue
                else:
                    new_b.add(bl)
            current_rule = (current_rule[0],frozenset(new_b)) 
            if max_vars is not None and len(used_vars) > max_vars:
                valid = False
                break

        if not valid:
            continue

        # current_rule = normalise_body_var(current_rule, initial_vars)
        results.add(current_rule)

    return results




def relax_join_sim_pairs(rule, max_vars):
    """
    Generate all rules obtained by resolving join–similarity
    co-occurring attribute pairs in all possible permutations.
    """

    head, body = rule
    body = set(body)

    # collect variables
    def vars_in_body(b):
        return {
            x for lit in b
            for x in lit.arguments
            if isinstance(x, int)
        }

    # group attribute atoms by value variable
    att_by_val = {}
    for lit in body:
        if lit.predicate == "att":
            att_by_val.setdefault(lit.arguments[2], []).append(lit)

    # find sim(v,v)
    sim_self = {
        lit.arguments[0]
        for lit in body
        if lit.predicate == "sim" and lit.arguments[0] == lit.arguments[1]
    }

    # collect join–similarity attribute pairs
    attr_pairs = []
    for v in sim_self:
        atts = att_by_val.get(v, [])
        if len(atts) >= 2:
            for i in range(len(atts)):
                for j in range(i + 1, len(atts)):
                    attr_pairs.append((v, atts[i], atts[j]))

    if not attr_pairs:
        return None

    results = set()

    for perm in permutations(attr_pairs):
        cur_body = set(body)
        used_vars = vars_in_body(cur_body)

        valid = True

        for v, att1, att2 in perm:
            # pick fresh variable
            v_new = None
            for x in range(max_vars):
                if x not in used_vars:
                    v_new = x
                    break
            if v_new is None:
                valid = False
                break

            # choose a deterministic side to break:
            # always replace att2 (order already encoded by permutation)
            to_replace = att2

            new_body = set()
            for lit in cur_body:
                if lit == to_replace:
                    tid, attr, _ = lit.arguments
                    new_body.add(
                        Literal("att", (tid, attr, v_new))
                    )
                elif lit.predicate == "sim" and lit.arguments == (v, v):
                    # similarity now links distinct variables
                    new_body.add(
                        Literal("sim", (v, v_new))
                    )
                else:
                    # tid, attr, vo = lit.arguments
                    # if vo == v:
                        
                    new_body.add(lit)

            cur_body = new_body
            used_vars.add(v_new)

        if valid:
            results.add((head, frozenset(cur_body)))

    return results



def relax_marked_join_pairs(rule, max_vars):
    """
    Generate all valid breakings of join–similarity occurrences.

    Only breaks joins caused by sim(V,V), and only by replacing
    attribute atoms — never similarity atoms directly.
    """
    head, body = rule
    body = list(body)

    # Collect all variables in the rule
    all_vars = {arg for lit in body for arg in lit.arguments if is_int(arg)}
    next_var = max(all_vars, default=-1) + 1

    # Index attribute and similarity atoms
    att_atoms = []
    sim_atoms = []

    for lit in body:
        if lit.predicate == 'att':
            att_atoms.append(lit)
        elif lit.predicate == 'sim':
            sim_atoms.append(lit)

    results = set()

    # Find variables V such that sim(V,V) exists
    sim_self_vars = {
        v for lit in sim_atoms
        if lit.arguments[0] == lit.arguments[1]
        for v in [lit.arguments[0]]
    }

    for V in sim_self_vars:
        # Attribute atoms containing V
        att_with_V = [
            lit for lit in att_atoms if V in lit.arguments
        ]

        # Must be a join (≥2 occurrences)
        if len(att_with_V) < 2:
            continue

        # For each way of breaking the join
        for broken_att in att_with_V:
            V_new = next_var
            next_var += 1

            new_body = []

            for lit in body:
                # --- Attribute atoms ---
                if lit.predicate == 'att':
                    if lit is broken_att:
                        new_args = tuple(
                            V_new if arg == V else arg
                            for arg in lit.arguments
                        )
                        new_body.append(
                            Literal(lit.predicate, new_args)
                        )
                    else:
                        new_body.append(lit)

                elif lit.predicate == 'sim':
                    x, y = lit.arguments

                    # self-similarity: sim(V,V)
                    if x == V and y == V:
                        new_body.append(
                            Literal('sim', (V_new, V))
                        )

                    # sim(V,X)
                    elif x == V:
                        new_body.append(
                            Literal('sim', (V_new, y))
                        )

                    # sim(X,V)
                    elif y == V:
                        new_body.append(
                            Literal('sim', (x, V_new))
                        )
                    else:
                        new_body.append(lit)
                else:
                    new_body.append(lit)


            results.add((head, frozenset(new_body)))

    return results



def gen_dup_structure(rule, max_literals):
    """
    Generate all rules longer than the input rule up to max_literals,
    using only duplicate structures of the existing rule.

    Only tuple variables are allowed to be fresh.
    Attribute names and value variables must already exist in the rule.
    """

    head, body = rule
    body = set(body)

    original_size = len(body)
    if original_size >= max_literals:
        return set()

    # -----------------------------
    # Extract structural templates
    # -----------------------------

    relational_preds = set()
    attr_templates = set()   # (attr_name, value_var)

    all_vars = set()

    for lit in body:
        if lit.predicate == 'att':
            tid, attr, val = lit.arguments
            attr_templates.add((attr, val))
            if isinstance(tid, int):
                all_vars.add(tid)
            if isinstance(val, int):
                all_vars.add(val)

        elif len(lit.arguments) == 1:
            relational_preds.add(lit.predicate)
            arg = lit.arguments[0]
            if isinstance(arg, int):
                all_vars.add(arg)

    if not all_vars:
        next_var = 0
    else:
        next_var = max(all_vars) + 1

    results = set()

    # -----------------------------------
    # Build possible duplicate structures
    # -----------------------------------

    duplicate_blocks = []

    for rel in relational_preds:
        for attr, val in attr_templates:

            fresh_tid = next_var
            next_var += 1

            rel_lit = head.__class__(rel, (fresh_tid,))
            att_lit = head.__class__('att', (fresh_tid, attr, val))

            duplicate_blocks.append({rel_lit, att_lit})

    # --------------------------------------------------
    # Add combinations of duplicate blocks up to limit
    # --------------------------------------------------

    for r in range(1, max_literals - original_size + 1):
        for combo in combinations(duplicate_blocks, r):

            new_body = set(body)

            for block in combo:
                new_body.update(block)

            if len(new_body) <= max_literals and len(new_body) > original_size:
                results.add((head, frozenset(new_body)))

    return results



def relax_marked_join_pairs2(rule):
    """
    Break all self-similarity joins simultaneously.

    For each self-sim variable V:
        - choose one attribute occurrence to break
    Generate all combinations across variables.
    """

    head, body = rule
    body = list(body)

    # Collect integer variables
    all_vars = {
        arg for lit in body
        for arg in lit.arguments
        if isinstance(arg, int)
    }
    next_var_base = max(all_vars, default=-1) + 1

    # Separate atoms
    att_atoms = []
    sim_atoms = []

    for lit in body:
        if lit.predicate == 'att':
            att_atoms.append(lit)
        elif lit.predicate == 'sim':
            sim_atoms.append(lit)

    # Identify self-sim variables and their break options
    break_options = {}  # V -> list of attribute atoms containing V

    for lit in sim_atoms:
        x, y = lit.arguments
        if x == y:
            V = x
            atts = [a for a in att_atoms if V in a.arguments]
            if len(atts) >= 2:
                break_options[V] = atts

    if not break_options:
        return set()

    break_vars = list(break_options.keys())

    results = set()

    # ----------------------------------------------------
    # Cross product over break choices for each variable
    # ----------------------------------------------------
    for chosen_atts in product(*(break_options[V] for V in break_vars)):

        # Map each V to a fresh variable
        fresh_map = {}
        next_var = next_var_base

        for V in break_vars:
            fresh_map[V] = next_var
            next_var += 1

        new_body = []

        for lit in body:

            # -------------------------
            # Attribute atoms
            # -------------------------
            if lit.predicate == 'att':

                replaced = False

                for V, broken_att in zip(break_vars, chosen_atts):
                    if lit is broken_att and V in lit.arguments:
                        V_new = fresh_map[V]
                        new_args = tuple(
                            V_new if arg == V else arg
                            for arg in lit.arguments
                        )
                        new_body.append(
                            Literal('att', new_args)
                        )
                        replaced = True
                        break

                if not replaced:
                    new_body.append(lit)

            # -------------------------
            # Similarity atoms
            # -------------------------
            elif lit.predicate == 'sim':
                x, y = lit.arguments
                nx = fresh_map.get(x, x)
                ny = fresh_map.get(y, y)

                # skip sim(V_new,V_new)
                if nx == ny and nx in fresh_map.values():
                    continue

                new_body.append(
                    Literal('sim', (nx, ny))
                )

            else:
                new_body.append(lit)

        results.add((head, frozenset(new_body)))

    return results



