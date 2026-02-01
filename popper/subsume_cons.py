from . trc_util import Rule, expand_rule_with_sim, comp, is_valid_rule, rule_to_nonground_meta_atoms, meta_atoms_to_cons, remove_comparison_from_body, cleanup_body
from . trc_util import non_empty_powerset, atoms_ranged_by_comparisons, body_atoms_linked_to_head_vars
from . util import Literal, Constraint, format_rule
from . trc_subsume import compute_core


def build_gen_cons(rule:Rule, range_pair)->set[tuple[int,str]]:
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
            meta_atoms = frozenset(rule_to_nonground_meta_atoms(sub_rule))
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
        
        
def build_spe_cons(rule:Rule, range_pair)->set[tuple[int,str]]:
    spe_cons = set()
    print("*** original rule:",format_rule(rule))
    core = compute_core(rule,range_pair)
    print("*** computed core:",format_rule(core))

    meta_atoms = frozenset(rule_to_nonground_meta_atoms(core))
    spe_cons.add((Constraint.SPECIALISATION,meta_atoms_to_cons(meta_atoms)))

    
    return spe_cons