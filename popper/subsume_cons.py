from . trc_util import Rule, expand_rule_with_sim, comp, is_valid_rule, rule_to_nonground_meta_atoms, meta_atoms_to_cons, is_body_connected
from . trc_util import non_empty_powerset, atoms_ranged_by_comparisons, body_atoms_linked_to_head_vars, normalise_body_var, collect_sim_var_pairs
from . trc_util import get_sim_symmetries
from . util import Literal, Constraint, format_rule, is_int
from . trc_subsume import compute_core, get_sim_specs, relax_join_sim_pairs, relax_marked_join_pairs,relax_marked_join_pairs2, gen_dup_structure
from itertools import combinations
from typing import Set
from copy import deepcopy



def build_gen_cons_meta(rule:Rule, range_pair)->set[tuple[int,str]]:
    gen_cons = set()
    meta_cons = set()
    # - 1 Build generalisation constraints (non-ground)
        #  - a. for those size<= size(r), valid subsequences of all pairings (expanded), and their variants (pruned as variable substitutions)
    # meta_atoms = rule_to_nonground_meta_atoms(rule)
    # gen_cons.add((Constraint.GENERALISATION,meta_atoms_to_cons(meta_atoms)))
    print("*** original rule:",format_rule(rule))
    expanded_rule = expand_rule_with_sim(rule)
    exh, _ = expanded_rule
    print("*** expanded rule:",format_rule(expanded_rule))
    all_comp = comp(expanded_rule)
    all_comp_ps = non_empty_powerset(all_comp)
    # for each subset, get together relational atoms
    head_related = body_atoms_linked_to_head_vars(expanded_rule)
    for elem in all_comp_ps:
        sub_body = atoms_ranged_by_comparisons(expanded_rule,elem)
        sub_body = sub_body.union(head_related)
        sub_rule = (exh,sub_body)
        print("     *** generated subrule:",format_rule(sub_rule))
        if is_valid_rule(sub_rule, range_pair):
            print("     *** Valid rule, add to constraint!")
            
            meta_atoms = rule_to_nonground_meta_atoms(sub_rule)
            meta_atoms.add(('body_size',0,len(sub_body)))
            meta_atoms = frozenset(meta_atoms)
            meta_cons.add(meta_atoms)
            
        # TO REMOVE
        else:
            print("     *** Invalid rule, skip!")
    for m in meta_cons:
        
        gen_cons.add((Constraint.GENERALISATION,meta_atoms_to_cons(m)))
    # TODO print(len(gen_cons))
        #  - b. for those size> size(r), for size = size(r) from b, duplicate relational atoms and some comparison atoms associated to the duplicates, 
        #       replace with a variable in max_var but not in r (while remain connected), then register as constraint
    
    return gen_cons
        # pass
        

     
def build_spe_cons_meta(rule:Rule, range_pair)->set[tuple[int,str]]:
    spe_cons = set()
    #print("*** original rule:",format_rule(rule))
    core = compute_core(rule,range_pair)
    #print("*** computed core:",format_rule(core))

    meta_atoms = frozenset(rule_to_nonground_meta_atoms(core))
    spe_cons.add((Constraint.SPECIALISATION,meta_atoms_to_cons(meta_atoms)))

    
    return spe_cons



def build_gen_rules(rule:Rule, range_pair,max_vars=6):
#->set[tuple[Literal,frozenset]]:
 #   gen_cons = set()
    # - 1 Build generalisation constraints (non-ground)
        #  - a. for those size<= size(r), valid subsequences of all pairings (expanded), and their variants (pruned as variable substitutions)
    # meta_atoms = rule_to_nonground_meta_atoms(rule)
    # gen_cons.add((Constraint.GENERALISATION,meta_atoms_to_cons(meta_atoms)))
    #print("*** original rule:",format_rule(rule))
    all_bvars = {x for lit in rule[1] for x in lit.arguments if is_int(x)}
    # print(all_bvars)
    expanded_rule = expand_rule_with_sim(rule)
    exh, _ = expanded_rule
    #print("*** expanded rule:",format_rule(expanded_rule))
    all_comp = comp(expanded_rule)
    #print(all_comp)
    all_comp_ps = non_empty_powerset(all_comp)
    seen = set()
    # for each subset, get together relational atoms
    head_related = body_atoms_linked_to_head_vars(expanded_rule)
    for elem in all_comp_ps:
        # print(elem)
        sub_body = atoms_ranged_by_comparisons(expanded_rule,elem)
        sub_body = sub_body.union(head_related)
        sub_rule = (exh,frozenset(sub_body))
        if not is_valid_rule(sub_rule, range_pair):
            continue
        norm_sub_rule = normalise_body_var(sub_rule, list(all_bvars))
        # awfully slow
        # print(" %%%% [start] compute relaxed subrules")     
        # relaxed_rules = relax_join_sim_pairs(norm_sub_rule,max_vars)
        # print(" %%%% [end] compute relaxed subrules")   
        if norm_sub_rule not in seen:
            # print("     *** generated subrule:",format_rule(norm_sub_rule))
            seen.add(norm_sub_rule)
            # print("     *** subrule added")
            # if relaxed_rules:
            #     for rl in relaxed_rules:
            #         if rl not in seen: 
            #             # print("     *** generated relaxed subrule:",format_rule(rl))
            #             seen.add(rl)
                        # print("     *** relaxed subrule added")
            #print("     *** Valid rule, add to constraint!")
    
    return seen
    # TODO print(len(gen_cons))
        #  - b. for those size> size(r), for size = size(r) from b, duplicate relational atoms and some comparison atoms associated to the duplicates, 
        #       replace with a variable in max_var but not in r (while remain connected), then register as constraint
    
    # return gen_cons
    #     # pass
def build_gen_rules3(rule: Rule, range_pair, max_vars=6):
    #print("*** original rule:", format_rule(rule))

    head, body = rule
    expanded_rule = expand_rule_with_sim(rule)
    exh, exp_body = expanded_rule
    #print("*** expanded rule:", format_rule(expanded_rule))

    # ---- PRECOMPUTATION ----
    all_bvars = {x for lit in exp_body for x in lit.arguments if is_int(x)}
    head_related = body_atoms_linked_to_head_vars(expanded_rule)
    all_comp = tuple(comp(expanded_rule))  # tuple for indexing

    # Cache for ranged bodies
    ranged_cache = {}

    seen = set()

    # ---- POWESET ITERATION ----
    for r in range(1, len(all_comp) + 1):
        for elem in combinations(all_comp, r):
            elem_key = frozenset(elem)

            # ---- ranged body (cached) ----
            if elem_key not in ranged_cache:
                sub_body = atoms_ranged_by_comparisons(expanded_rule, elem)
                sub_body |= head_related
                ranged_cache[elem_key] = frozenset(sub_body)
            else:
                sub_body = ranged_cache[elem_key]

            sub_rule = (exh, frozenset(sub_body))

            # ---- EARLY PRUNING ----
            if not is_valid_rule(sub_rule, range_pair):
                continue

            # ---- NORMALISATION ----
            # norm_rule = normalise_body_var(sub_rule, list(all_bvars))

            if sub_rule in seen:
                continue
            #print(f" %%%% add subrules {format_rule(sub_rule)}")     
            seen.add(sub_rule)
            
            # ---- RELAXATION (only if new) ----
            # relaxed_rules = relax_marked_join_pairs(sub_rule, max_vars)
            relaxed_rules = relax_marked_join_pairs2(sub_rule)
               
            if relaxed_rules:
                for rl in relaxed_rules:
                    if rl not in seen:
                        #print(f" %%%% add relaxed subrules {format_rule(rl)}")     
                        seen.add(rl)

    return seen
     
def build_gen_rules4(rule: Rule, range_pair, attr_bias:dict = None, sim_defined:set = None):
    
    def exc_symmetry(results):
        for s in results.copy():
            s_symmetries = get_sim_symmetries(s)
            # for  ss in s_symmetries:
            #     print(f" %%%% excluding symmetry {format_rule(ss)}")
        return s_symmetries
    # print("*** original rule:", format_rule(rule))

    head, body = rule
    expanded_rule = expand_rule_with_sim(rule,attr_bias,sim_defined=sim_defined)
    exh, exp_body = expanded_rule
    # print("*** expanded rule:", format_rule(expanded_rule))
    results = set()
    results.add(rule)
    # gen_core = compute_core(rule=rule,range_pair=range_pair)
    # redundant_gens = gen_dup_structure(gen_core,max_lit)
    # for rg in redundant_gens:
    #     if is_valid_rule(rg,range_pair=range_pair):
    #         results.add(rg)
    
    
    if expanded_rule == rule:
        results =results.union(exc_symmetry(results))
        return results

    # ---- PRECOMPUTATION ----
    all_bvars = {x for lit in exp_body for x in lit.arguments if is_int(x)}
    head_related = body_atoms_linked_to_head_vars(expanded_rule)
    all_comp = comp(expanded_rule)  # tuple for indexing
    marked_join_comps = {c for c in all_comp if tuple(list(c)[:-1]+[0]) in all_comp and tuple(list(c)[:-1]+[1]) in all_comp}
    # Cache for ranged bodies
    ranged_cache = {}
    
    checked = set()
    # TODO print(len(gen_cons))
    #  - b. for those size> size(r), for size = size(r) from b, duplicate relational atoms and some comparison atoms associated to the duplicates, 
    #       replace with a variable in max_var but not in r (while remain connected), then register as constraint

    # compute join relaxations of the rule
    # ---- POWESET ITERATION ----
    for r in range(1, len(marked_join_comps) + 1):
        for elem in combinations(marked_join_comps, r):
            elem_key = frozenset(elem)

            # ---- ranged body (cached) ----
            if elem_key not in ranged_cache:
                new_body = atoms_ranged_by_comparisons(expanded_rule, elem)
                new_body = new_body.union(body)
                
                ranged_cache[elem_key] = frozenset(new_body)
            else:
                new_body = ranged_cache[elem_key]
                # print(new_body)

            marked_rule = (exh, frozenset(new_body))
            if marked_rule in checked:
                continue
            # ---- EARLY PRUNING ----
            if not is_valid_rule(marked_rule, range_pair):
                continue
            checked.add(marked_rule)
            # ---- NORMALISATION ----
            # norm_rule = normalise_body_var(sub_rule, list(all_bvars))

            # if marked_rule in seen:
            #     continue
            # print(f" %%%% marked rule {format_rule(marked_rule)}")     
            # seen.add(sub_rule)
            
            # ---- RELAXATION (only if new) ----
            relaxed_rules = relax_marked_join_pairs2(marked_rule)
               
            if relaxed_rules:
                for rl in relaxed_rules:
                    if rl not in results:
                        # len_seen = len(results)
                        results.add(rl)
                        # len_seen_ = len(results)
                        # if len_seen_ != len_seen:
                        #     print(f" %%%% add relaxed subrules {format_rule(rl)}")   

        results = results.union(exc_symmetry(results=results))
        
    return results
     

def build_gen_rules2(rule: Rule, range_pair) -> Set[Rule]:
    """
    Generate generalized rules from `rule` that align with `range_pair`.
    Optimizations:
      - lazy powerset generation
      - caching ranged bodies
      - caching normalization
      - early pruning (connectivity)
      - deterministic variable handling
    """

    exh, body = rule

    # collect all body variables once (deterministic order)
    all_bvars = sorted(
        {x for lit in body for x in lit.arguments if is_int(x)}
    )

    # expand rule with similarity atoms only once
    expanded_rule = expand_rule_with_sim(rule)
    exh, expanded_body = expanded_rule

    # all comparison atoms (tuple, not set → deterministic iteration)
    all_comp = tuple(comp(expanded_rule))

    # atoms that must always stay (linked to head variables)
    head_related = frozenset(
        body_atoms_linked_to_head_vars(expanded_rule)
    )

    seen: Set[Rule] = set()

    # caches to avoid recomputation
    ranged_cache = {}   # comparison subset -> body atoms
    norm_cache = {}     # frozenset(body atoms) -> normalized rule

    # iterate lazily over non-empty subsets of comparisons
    for size in range(1, len(all_comp) + 1):
        for comp_subset in combinations(all_comp, size):

            # compute ranged atoms only once per subset
            if comp_subset not in ranged_cache:
                ranged_cache[comp_subset] = atoms_ranged_by_comparisons(
                    expanded_rule, comp_subset
                )

            # always include head-related atoms
            sub_body = ranged_cache[comp_subset] | head_related

            # ---- cheap pruning before expensive operations ----
            if not is_body_connected((exh,sub_body)):
                continue

            body_key = frozenset(sub_body)

            # normalize once per distinct body
            if body_key not in norm_cache:
                sub_rule = (exh, body_key)
                norm_cache[body_key] = normalise_body_var(
                    sub_rule, all_bvars
                )

            norm_sub_rule = norm_cache[body_key]

            # final semantic check
            if is_valid_rule(norm_sub_rule, range_pair):
                seen.add(norm_sub_rule)
    print(f"** Generated {str(len(seen))} generalisations")
    return seen
     
def build_spe_rule(rule:Rule, range_pair, max_vars = 6, sim_defined = None)->tuple[Literal,frozenset]:
    # spe_cons = set()
    # print("*** original rule:",format_rule(rule))
    all_spec_cores = set()
    # all_bvars = sorted(
    #     {x for lit in rule[1] for x in lit.arguments if is_int(x)}
    # )
    # print(all_bvars)
    core = compute_core(rule,range_pair)
    #print("*** computed core:",format_rule(core))
    # core = normalise_body_var(
    #                 core, all_bvars
    #             )
    all_spec_cores.add(core)
    pairs = collect_sim_var_pairs(rule)
    #print("*** [Start] finding sim specialisations of core")
    if pairs:
        sim_specs = get_sim_specs(core,pairs,max_vars)
        if sim_specs:
            all_spec_cores.union(sim_specs)
     #       [print("*** sim spec of computed core:",format_rule(c)) for c in sim_specs] 
    #print("*** [end] sim specialisations of core")
    # meta_atoms = frozenset(rule_to_nonground_meta_atoms(core))
    # spe_cons.add((Constraint.SPECIALISATION,meta_atoms_to_cons(meta_atoms)))
    #print("*** [Start] building sim symmetries of specialisation core")
    for s in all_spec_cores.copy():
        s_symmetries = get_sim_symmetries(s)
        # for  ss in s_symmetries:
        #      print(f" %%%% excluding symmetry {format_rule(ss)}")
        all_spec_cores = all_spec_cores.union(s_symmetries)
    #print("*** [end] building sim symmetries of specialisation core")
    return all_spec_cores

