from . util import  Literal
from typing import Tuple, Set, FrozenSet
from itertools import combinations
from collections import defaultdict, deque
from itertools import combinations, chain
from copy import deepcopy

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

def is_body_connected(rule) -> bool:
    """
    Check whether the body of a rule is connected according to the formal definition.
    """
    _, body = rule

    # --- Step 1: collect tuple variables ---
    tuple_vars = set()
    att_atoms = []
    sim_atoms = []

    for lit in body:
        if lit.predicate == 'att':
            tid, att, var = lit.arguments
            tuple_vars.add(tid)
            att_atoms.append(lit)
        elif lit.predicate == 'sim':
            sim_atoms.append(lit)
        else:
            # relational atom
            tuple_vars.add(lit.arguments[0])

    # Trivial cases
    if len(tuple_vars) <= 1:
        return True

    # --- Step 2: build connectivity graph ---
    graph = defaultdict(set)

    # (1) join connectivity: same value variable
    for a1, a2 in combinations(att_atoms, 2):
        tid1, _, var1 = a1.arguments
        tid2, _, var2 = a2.arguments
        if tid1 != tid2 and var1 == var2:
            graph[tid1].add(tid2)
            graph[tid2].add(tid1)

    # (2) similarity connectivity
    # map value var -> tuple vars using it
    var_to_tids = defaultdict(set)
    for lit in att_atoms:
        tid, _, var = lit.arguments
        var_to_tids[var].add(tid)

    for sim in sim_atoms:
        v1, v2 = sim.arguments
        for t1 in var_to_tids.get(v1, []):
            for t2 in var_to_tids.get(v2, []):
                if t1 != t2:
                    graph[t1].add(t2)
                    graph[t2].add(t1)

    # --- Step 3: connectivity check ---
    start = next(iter(tuple_vars))
    visited = {start}
    queue = deque([start])

    while queue:
        current = queue.popleft()
        for nbr in graph[current]:
            if nbr not in visited:
                visited.add(nbr)
                queue.append(nbr)

    return visited == tuple_vars


def is_range_safe(rule:Rule) -> bool:
    """
    Checks whether:
      (1) every attribute atom's tid appears in some relational atom
      (2) every sim-variable appears as a value variable of some attribute atom
    """
    _, body = rule

    rel_tids = set()
    att_tids = set()
    att_value_vars = set()
    sim_vars = set()

    for lit in body:
        if lit.predicate == 'att':
            tid, _, var = lit.arguments
            att_tids.add(tid)
            att_value_vars.add(var)
        elif lit.predicate == 'sim':
            v1, v2 = lit.arguments
            sim_vars.add(v1)
            sim_vars.add(v2)
        else:
            # relational atom
            rel_tids.add(lit.arguments[0])

    # (1) dangling attribute atoms
    if not att_tids.issubset(rel_tids):
        return False

    # (2) dangling similarity variables
    if not sim_vars.issubset(att_value_vars):
        return False

    return True

def is_valid_rule(rule:Rule, range_pair)->bool:
    # h,body = rule
    # hvar_map = dict()
    # for hv in h.arguments:
    #     for b in body:
    #         if b.predicate == 'att': 
    #             if b.arguments[-1] == hv:
    #                 hvar_map[hv] = b
    # for hv in h.arguments:
    #     if hv not in hvar_map:
    #         return False
    if not rule_aligns_with_range_pair(rule,range_pair):
        return False
    # check is there any unbounded literals
    return is_range_safe(rule) and is_body_connected(rule)

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



    # head_tuple1 = {literal.arguments for literal in b1 if literal.predicate == 'att' and (literal.arguments[-1] == h1.arguments[0] or literal.arguments[-1] == h1.arguments[1])}
    # head_tuple2 = {literal.arguments for literal in b2 if literal.predicate == 'att' and (literal.arguments[-1] == h1.arguments[0] or literal.arguments[-1] == h1.arguments[1])}
    # if len(head_tuple1)!=len(head_tuple2):
    #     return False
    # range_pair_head1 = {(r.predicate,lit_args[1]) for r in rel(r1)  for lit_args in head_tuple1 if r.arguments[0] == lit_args[0]}
    # range_pair_head2 = {(r.predicate,lit_args[1]) for r in rel(r2)  for lit_args in head_tuple2 if r.arguments[0] == lit_args[0]}
    # if range_pair_head1!=range_pair_head2:
    #     return False
    # return containment_check(b1h,b2)




    
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


def expand_rule_with_sim(rule):
    """
    Given a rule, return a new rule where for every join in the body
    (i.e., multiple att-atoms sharing the same value variable),
    similarity atoms sim(v1, v2) are added for the joined variables.

    Joins of arity > 2 generate all pairwise similarity atoms.
    Existing sim-atoms are preserved, duplicates are avoided.
    """
    head, body = rule
    new_body = set(deepcopy(body))

    # Collect attribute atoms grouped by value variable
    # value_var -> list of (tid, attr_name)
    value_var_groups = {}
    for lit in body:
        if lit.predicate == 'att':
            tid, attr, val_var = lit.arguments
            value_var_groups.setdefault(val_var, []).append((tid, attr))

    # For each join group, add similarity atoms
    for val_var, att_list in value_var_groups.items():
        if len(att_list) >= 2:
            # Multi-attribute join: generate all pairwise sim atoms
            for _ in combinations(att_list, 2):
                sim_atom = Literal('sim', (val_var, val_var))
                new_body.add(sim_atom)

    return (head, new_body)



def rule_to_meta_atoms(rule):
    """
    Convert a rule into a set of meta-atoms.

    Head literal:
      head_literal(C, predicate, arity, arguments)

    Body literals:
      body_literal(C, predicate, arity, arguments)

    For relational atoms (arity == 1), arguments is the integer itself.
    For all others, arguments is the full argument tuple.
    """
    head, body = rule
    meta_atoms = set()

    # Handle head
    if head is not None:
        head_pred = head.predicate
        head_args = head.arguments
        head_arity = len(head_args)

        meta_atoms.add((
            'head_literal',
            'C',
            head_pred,
            head_arity,
            head_args
        ))

    # Handle body
    for lit in body:
        pred = lit.predicate
        args = lit.arguments
        arity = len(args)

        # Relational atom special case
        if arity == 1:
            arg_repr = args[0]
        else:
            arg_repr = args

        meta_atoms.add((
            'body_literal',
            'C',
            pred,
            arity,
            arg_repr
        ))

    return meta_atoms


def rule_to_nonground_meta_atoms(rule):
    """
    Convert a rule into a set of meta-atoms.

    All integers in argument positions are rewritten as variables V{int}.

    Head literal:
      head_literal(C, predicate, arity, arguments)

    Body literals:
      body_literal(C, predicate, arity, arguments)

    For relational atoms (arity == 1), arguments is the single variable.
    """
    head, body = rule
    meta_atoms = set()

    def lift_arg(arg):
        """Convert an argument into its meta representation."""
        if isinstance(arg, int):
            return f"V{arg}"
        return arg

    def lift_args(args):
        return tuple(lift_arg(a) for a in args)

    # Handle head
    if head is not None:
        head_pred = head.predicate
        head_args = lift_args(head.arguments)
        head_arity = len(head_args)

        meta_atoms.add((
            'head_literal',
            'C',
            head_pred,
            head_arity,
            head_args
        ))

    # Handle body
    for lit in body:
        pred = lit.predicate
        args = lit.arguments
        arity = len(args)

        if arity == 1:
            # relational atom: single variable
            arg_repr = lift_arg(args[0])
        else:
            arg_repr = lift_args(args)

        meta_atoms.add((
            'body_literal',
            'C',
            pred,
            arity,
            arg_repr
        ))

    return meta_atoms



def meta_atoms_to_cons(meta_atoms):
    """
    Given a set of meta-atoms, return an ASP constraint string of the form:

        :- b1, b2, ..., bn.

    where each bi is a ground ASP atom constructed from the meta-atoms.
    """

    def atom_to_asp(atom):
        name = atom[0]
        args = atom[1:]

        def fmt(a):
            if isinstance(a, tuple):
                return "(" + ",".join(fmt(x) for x in a) + ")"
            elif isinstance(a, str):
                return a
            else:
                return str(a)

        return f"{name}({','.join(fmt(a) for a in args)})"

    if not meta_atoms:
        return ":-."

    body_atoms = sorted(atom_to_asp(a) for a in meta_atoms)
    return ":- " + ", ".join(body_atoms) + "."


def non_empty_powerset(iterable):
    s = tuple(iterable)
    return chain.from_iterable(combinations(s, r) for r in range(1, len(s)+1))


def atoms_ranged_by_comparisons(rule, comparisons):
    """
    Given a rule and a set of comparisons, return the set of
    relational atoms and attribute atoms participating in them.

    comparison format:
      (t1, att1, t2, att2, comp_type)
      comp_type: 0 = join, 1 = similarity
    """
    _, body = rule

    # Index atoms for fast lookup
    rel_atoms = {
        lit.arguments[0]: lit
        for lit in body
        if lit.predicate != 'att' and len(lit.arguments) == 1
    }

    att_atoms = {}
    for lit in body:
        if lit.predicate == 'att':
            tid, att_name, var = lit.arguments
            att_atoms.setdefault((tid, att_name), []).append(lit)

    ranged_atoms = set()

    for (t1, att1, t2, att2, _) in comparisons:
        # attribute atoms
        for lit in att_atoms.get((t1, att1), []):
            ranged_atoms.add(lit)
        for lit in att_atoms.get((t2, att2), []):
            ranged_atoms.add(lit)

        # corresponding relational atoms
        if t1 in rel_atoms:
            ranged_atoms.add(rel_atoms[t1])
        if t2 in rel_atoms:
            ranged_atoms.add(rel_atoms[t2])

    return ranged_atoms



def body_atoms_linked_to_head_vars(rule):
    """
    Return all body atoms (attribute or similarity atoms) that
    contain variables appearing in the rule head.
    """
    head, body = rule

    if head is None:
        return set()

    # variables appearing in the head
    head_vars = set(head.arguments)

    linked_atoms = set()

    for lit in body:
        if lit.predicate == 'att':
            tid, _, var = lit.arguments
            if tid in head_vars or var in head_vars:
                linked_atoms.add(lit)

        elif lit.predicate == 'sim':
            v1, v2 = lit.arguments
            if v1 in head_vars or v2 in head_vars:
                linked_atoms.add(lit)

    return linked_atoms



def rule_aligns_with_range_pair(rule, range_pair):
    """
    Check whether a rule aligns with a given range pair.

    range_pair format:
        ((rel_pred1, att_name1), (rel_pred2, att_name2))
    """
    head, body = rule

    if head is None or len(head.arguments) != 2:
        return False

    h0, h1 = head.arguments
    (rp1, rp2) = range_pair

    # index relational atoms by tuple variable
    rel_by_tid = {
        lit.arguments[0]: lit.predicate
        for lit in body
        if lit.predicate != 'att' and len(lit.arguments) == 1
    }

    # collect (var, rel_pred, att_name) for head-attached attributes
    head_att_triples = set()
    for lit in body:
        if lit.predicate == 'att':
            tid, att_name, var = lit.arguments
            if var == h0 or var == h1:
                if tid not in rel_by_tid:
                    continue
                head_att_triples.add((var, rel_by_tid[tid], att_name))

    # existence checks (symmetry allowed)
    def exists_match(v1, rp1, v2, rp2):
        return (
            (v1, rp1[0], rp1[1]) in head_att_triples and
            (v2, rp2[0], rp2[1]) in head_att_triples
        )

    return (
        exists_match(h0, rp1, h1, rp2)
        or
        exists_match(h0, rp2, h1, rp1)
    )