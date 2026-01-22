import time
import re
import clingo
import numbers
import clingo.script
import pkg_resources
from . util import Constraint, Literal, is_int
from clingo import Function, Number, Tuple_
from itertools import permutations

def arg_to_symbol(arg):
    if isinstance(arg, tuple):
        return Tuple_(tuple(arg_to_symbol(a) for a in arg))
    if isinstance(arg, numbers.Number):
        return Number(arg)
    if isinstance(arg, str):
        return Function(arg)

def atom_to_symbol(pred, args):
    xs = tuple(arg_to_symbol(arg) for arg in args)
    return Function(name = pred, arguments = xs)

DEFAULT_HEURISTIC = """
#heuristic size(N). [1000-N,true]
"""

NOISY_ENCODING = """
program_bounds(0..K):- max_size(K).
program_size_at_least(M):- size(N), program_bounds(M), M <= N.
"""

class Generator:

    def __init__(self, settings, bkcons=[]):
        self.savings = 0
        self.settings = settings
        self.cached_clingo_atoms = {}
        self.handle = None
        self.pruned_sizes = set()

        encoding = []
        alan = pkg_resources.resource_string(__name__, "lp/alan.pl").decode()
        encoding.append(alan)

        with open(settings.bias_file) as f:
            bias_text = f.read()
        bias_text = re.sub(r'max_vars\(\d*\).','', bias_text)
        bias_text = re.sub(r'max_body\(\d*\).','', bias_text)
        bias_text = re.sub(r'max_clauses\(\d*\).','', bias_text)

        for p,a in settings.pointless:
            bias_text = re.sub(rf'body_pred\({p},\s*{a}\)\.', '', bias_text)
            bias_text = re.sub(rf'constant\({p},.*?\).*', '', bias_text, flags=re.MULTILINE)

        encoding.append(bias_text)
        encoding.append(f'max_clauses({settings.max_rules}).')
        encoding.append(f'max_body({settings.max_body}).')
        encoding.append(f'max_vars({settings.max_vars}).')

        # ADD VARS, DIRECTIONS, AND TYPES
        head_arity = len(settings.head_literal.arguments)
        # encoding.append(f'head_vars({head_arity}, {tuple(range(head_arity))}).')
        h_args_str = ','.join(map(str, range(head_arity)))
        encoding.append(f'head_vars({head_arity}, ({h_args_str})).')
        arities = set(a for p, a in self.settings.body_preds)
        arities.add(head_arity)
        vars_list = []
        # print('----------', settings.max_vars, arities)
        for arity in arities:
            for xs in permutations(range(settings.max_vars), arity):
                vars_list.append((arity, tuple(xs)))
                xs_str = ', '.join(str(x) for x in xs)
                # !! Leon too restricted?
                if arity!=3:
                    encoding.append(f'vars({arity}, ({xs_str})).')
                    for i, x in enumerate(xs):
                        encoding.append(f'var_pos({x}, ({xs_str}), {i}).')
                    sorted_xs_str = ', '.join(str(x) for x in tuple(sorted(xs)))
                    encoding.append(f'ordered_vars(({xs_str}), ({sorted_xs_str})).')
                # encoding.append(f'ordered_vars({tuple(xs)},{tuple(sorted(xs))}).')
                
        ## Leon: added to create vars with fixed-position constants from attrbute atoms from a schema in bias file
        # to update
        # - find const-facts, get predicate and its position that is constant
        # - get arity of the predicate
        # - iterate through vars_list to find vars with same arity
        # - for each vars with same arity, replace the variable at the constant position with a constant of attribute name
        schema_attr_patt = re.compile(
            r"^\s*attr\s*\(\s*"
            r"([a-z0-9_]+)\s*,\s*"   # arg1
            r"([0-9]+)\s*"
            r"\)\s*\.\s*$",
            re.MULTILINE
        )

        schema_attr_tups = []
        for match in schema_attr_patt.finditer(bias_text):
            schema_attr_tups.append(match.groups())        
        for arity, xs in vars_list:
            for att_tup in schema_attr_tups:
                 # if the attribute is not a tid
                if arity == 3 and int(att_tup[-1])!= 0:
                        # Leon: modified to support symmetry breaking ordering
                        # xs_vars = sorted((xs[0],xs[2]))
                        xs_vars = sorted((0,xs[0],xs[2]))
                        xs = list(xs)
                        xs[1] = att_tup[0]
                        xs_str = ', '.join(str(x) for x in xs)
                        encoding.append(f'vars({arity}, ({xs_str})).')
                        for i, x in enumerate(xs):
                            if is_int(x):
                                encoding.append(f'var_pos({x}, ({xs_str}), {i}).')
                            else:
                                encoding.append(f'const_pos({x}, ({xs_str}), {i}).')
                        # Leon: modified to support symmetry breaking ordering, constant position assigns 0
                        # ordered_xs_str = ', '.join(str(x) for x in tuple((xs_vars[0],xs[1],xs_vars[1])))
                        ordered_xs_str = ', '.join(str(x) for x in xs_vars)
                        encoding.append(f'ordered_vars(({xs_str}),({ordered_xs_str})).')
        # ORDERING THINGY
        # %% appears((0,0,V0)):- body_literal(_, _, _, (V0,)), not head_var(_,V0).
        # appears((0,V0,V1)):- body_literal(_, _, _, (A,B)), ordered_vars((A,B), (V0,V1)).
        # appears((V0,V1,V2)):- body_literal(_, _, _, (A,B,C)), ordered_vars((A,B,C), (V0,V1,V2)).
        order_cons = []
        max_arity = max(arities)
        for arity in range(2, max_arity+1):
            xs1 = ','.join(f'V{i}' for i in range(arity)) # Vs
            xs2 = ','.join(f'X{i}' for i in range(arity)) # Xs

            if arity < max_arity:
                prefix = ','.join(str(0) for i in range(arity, max_arity)) + ',' + xs1
            else:
                prefix = xs1


            order_cons.append(f'appears(({prefix})):- body_literal(_,_,_,({xs2})), ordered_vars(({xs2}), ({xs1})).')

            order_cons.append(f'var_tuple(({prefix})):- body_pred(P,{arity}), vars({arity},Vars), not bad_body(P,Vars), not type_mismatch(P,Vars), ordered_vars(Vars,OrderedVars), OrderedVars=({xs1}).')


            if arity == 1:
                order_cons.append(f'var_member(V,(0,0,0,V)):-var(V).')
            else:
                order_cons.append(f'var_member(V,({prefix})):-vars(_, Vars), Vars=({xs1}), var_member(V,Vars).')
            # print(f)
            # var_member(V,(0,0,V0,V1)):-vars(_, Vars), Vars=(V0,V1), var_member(V,Vars).
            # var_member(V,(0,V0,V1,V2)):-vars(_, Vars), Vars=(V0,V1,V2), var_member(V,Vars).

        xs1 = ','.join(f'V{i}' for i in range(max_arity)) # Vs
        for k in range(max_arity):
            xs2 = ','.join(f'V{i}' for i in range(k)) # Vs
            if k > 0 and k < max_arity:
                xs2 += ','
            xs2 += ','.join(f'X{i}' for i in range(k, max_arity))
            # added Leon to skip const position for counting symmetry breaking ordering
            skip_const_pos_lower = ''
            if max_arity == 3 and k ==1:
                skip_const_pos_lower = f', not const_pos(V{k}, Vars1, 1), Vars1 = ({xs1}), not const_pos(X{k},Vars2,1), Vars2 = ({xs2})'
            order_cons.append(f'lower(({xs1}),({xs2})):- var_tuple(({xs1})), var_tuple(({xs2})), X{k} < V{k} {skip_const_pos_lower}.')

        for k in range(max_arity-1):
            # A,B,C,D
            v0 = f'V{k}'
            v1 = f'V{k+1}'
            # added Leon (hack):
            skip_const_pos_seen_lower = ''
            skip_const_pos_gap_ = ''
            if max_arity == 3:
                skip_const_pos_seen_lower = ', not const_pos(V1, Vars1,1), not const_pos(V, Vars2, 1)'
                
            order_cons.append(f'seen_lower(Vars1, V):- V={v1}-1, Vars1 = ({xs1}), {v0} < V < {v1}, lower(Vars1, Vars2), var_tuple(Vars1), appears(Vars2), var_member(V, Vars2), not head_var(_,V) {skip_const_pos_seen_lower}.')
            
            # Leon: [solved] suspecting issue after allowing constants, where when V is grounded with non-integer constant, the operation V1-1 fails
            order_cons.append(f'gap_(({xs1}),{v1}-1):- var_tuple(({xs1})), {v0} < V < {v1}, var(V) {skip_const_pos_gap_}.')
        # added Leon (hack): 
        if max_arity == 3:
            order_cons.append('seen_lower(Vars1, V):- V=V2-1, Vars1 = (V0,V1,V2), V0 < V < V2, lower(Vars1, Vars2), var_tuple(Vars1), appears(Vars2), var_member(V, Vars2), not head_var(_,V), const_pos(V1, Vars1, 1).')
            count_const_pos_gap = 'gap_((V0,V1,V2),V2-1):- var_tuple((V0,V1,V2)), V0 < V < V2, var(V), const_pos(V1, (V0,V1,V2), 1).'
            order_cons.append(count_const_pos_gap)

        order_cons.append(f'gap(({xs1}),V):- gap_(({xs1}), _), #max' + '{X :gap_((' + xs1 + '), X)} == V.')

        order_cons.append(f':- appears(({xs1})), gap(({xs1}), V), not seen_lower(({xs1}),V), not head_var(_,V).')

        # print('\n'.join(order_cons))
        encoding.extend(order_cons)

        # print('========', self.settings.body_types)
        type_encoding = set()
        if self.settings.head_types:
            #### Leon: Origin code below ####
            # types = tuple(self.settings.head_types)
            # str_types = str(types).replace("'","")
            # type_encoding = set()
            # if self.settings.head_types:
            #     types = tuple(self.settings.head_types)
            #     str_types = str(types).replace("'","")
            #     for i, x in enumerate(self.settings.head_types):
            #         type_encoding.add(f'type_pos({str_types}, {i}, {x}).')

            #     for pred, types in self.settings.body_types.items():
            #         types = tuple(types)
            #         str_types = str(types).replace("'","")
            #         for i, x in enumerate(types):
            #             type_encoding.add(f'type_pos({str_types}, {i}, {x}).')
            #     encoding.extend(type_encoding)
            h_types = self.settings.head_types
            for t in h_types:
                h_type = tuple(t)
                # Leon: [bug] str(tuple) results to a string (t1,), leads to mismatch of types of unary predicate if declared as type(pred,(t1))
                #str_types = str(h_type).replace("'","")
                str_types = ','.join(str(x) for x in h_type)
                # print(str_types)
                for i, x in enumerate(h_type):
                    type_encoding.add(f'type_pos(({str_types}), {i}, {x}).')

            for pred, b_types in self.settings.body_types.items():
                for b_type in b_types:
                    b_type = tuple(b_type)
                    #str_types = str(b_type).replace("'","")
                    str_types = ','.join(str(x) for x in b_type)
                    for i, x in enumerate(b_type):
                        type_encoding.add(f'type_pos(({str_types}), {i}, {x}).')
            encoding.extend(type_encoding)

        for pred, xs in self.settings.directions.items():
            for i, v in xs.items():
                if v == '+':
                    encoding.append(f'direction_({pred}, {i}, in).')
                if v == '-':
                    encoding.append(f'direction_({pred}, {i}, out).')

        max_size = (1 + settings.max_body) * settings.max_rules
        if settings.max_literals < max_size:
            encoding.append(f'custom_max_size({settings.max_literals}).')

        if settings.noisy:
            encoding.append(NOISY_ENCODING)

        encoding.extend(bkcons)

        if settings.single_solve:
            encoding.append(DEFAULT_HEURISTIC)

        encoding = '\n'.join(encoding)

        # with open('ENCODING-GEN.pl', 'w') as f:
        #     f.write(encoding)

        if self.settings.single_solve:
            solver = clingo.Control(['--heuristic=Domain','-Wnone'])

        solver.configuration.solve.models = 0
        # TO REMOVE
        print(encoding)
        solver.add('base', [], encoding)
        solver.ground([('base', [])])
        self.solver = solver

    def update_solver(self, size):
        # not used when learning programs without pi or recursion
        pass

    def get_prog(self):
        if self.handle is None:
            self.handle = iter(self.solver.solve(yield_ = True))
        # TO REMOVE
        print('*** get next model')
        self.model = next(self.handle, None)
        if self.model is None:
            return None

        return self.parse_model_single_rule(self.model.symbols(shown = True))

    def parse_model_single_rule(self, model):
        # TO REMOVE
        print('*** parse_model_single_rule')
        settings = self.settings
        head = settings.head_literal
        body = set()
        cached_literals = settings.cached_literals
        # Leon: Fixed atoms of body_literals on vars position may contain constants failed to parse
        for atom in model:
            args = atom.arguments
            # pred: arg[1], tuple: vars
            body.add(cached_literals[args[1].name, tuple(args[3].arguments)])
        rule = head, frozenset(body)
        return frozenset({rule})

    def prune_size(self, size):
        if size in self.pruned_sizes:
            return
        self.pruned_sizes.add(size)
        size_con = [(atom_to_symbol("size", (size,)), True)]
        self.model.context.add_nogood(size_con)

    def constrain(self, tmp_new_cons):
        new_ground_cons = set()
        # new_ground_cons_typed = {}
        for xs in tmp_new_cons:
            con_type = xs[0]
            con_prog = xs[1]

            if con_type == Constraint.GENERALISATION or con_type == Constraint.BANISH:
                con_size = None
                if self.settings.noisy and len(xs)>2:
                    con_size = xs[2]
                # print('gen', con_type)
                ground_rules2 = tuple(self.build_generalisation_constraint3(con_prog, con_size))
                new_ground_cons.update(ground_rules2)
                # if int(con_type) in new_ground_cons_typed:
                #     new_ground_cons_typed[int(con_type)].update(ground_rules2)
                # else:
                #    new_ground_cons_typed[int(con_type)] =  set()
                #    new_ground_cons_typed[int(con_type)].update(ground_rules2)
            elif con_type == Constraint.SPECIALISATION:
                con_size = None
                if self.settings.noisy and len(xs)>2:
                    con_size = xs[2]
                ground_rules2 = tuple(self.build_specialisation_constraint3(con_prog, con_size))
                # if int(con_type) in new_ground_cons_typed:
                #     new_ground_cons_typed[int(con_type)].update(ground_rules2)
                # else:
                #    new_ground_cons_typed[int(con_type)] =  set()
                #    new_ground_cons_typed[int(con_type)].update(ground_rules2)              
                new_ground_cons.update(ground_rules2)
            elif con_type == Constraint.UNSAT:
                cons_ = self.unsat_constraint2(con_prog)
                # if int(con_type) in new_ground_cons_typed:
                #     new_ground_cons_typed[int(con_type)].update(cons_)
                # else:
                #    new_ground_cons_typed[int(con_type)] =  set()
                #    new_ground_cons_typed[int(con_type)].update(cons_)            
                new_ground_cons.update(cons_)
        # TO REMOVE        
        # [print(i,c) for i,c in new_ground_cons_typed.items()]
        tmp = self.model.context.add_nogood
        cached_clingo_atoms = self.cached_clingo_atoms

        for ground_body in new_ground_cons:

            # print(', '.join(sorted(map(str,ground_body))))
            nogood = []
            for sign, pred, args in ground_body:
                k = hash((sign, pred, args))
                try:
                    x = cached_clingo_atoms[k]
                except KeyError:
                    x = (atom_to_symbol(pred, args), sign)
                    cached_clingo_atoms[k] = x
                nogood.append(x)
            tmp(nogood)

    def unsat_constraint2(self, body):
        # if no types, remap variables
        if len(self.settings.body_types) == 0:
            _, body = remap_variables((None, body))
       
        # assignments = self.find_deep_bindings4(body)
        assignments = self.find_deep_bindings42(body)
        # [print(a) for a in assignments] 
        for assignment in assignments:
            rule = []
            for pred, args in body:
                
                if len(args) == 3 and str(pred) == 'att':
                    args2 = (assignment[args[0]],args[1],assignment[args[2]])
                else:
                    args2 = tuple(assignment[x] for x in args)
                rule.append((True, 'body_literal', (0, pred, len(args), args2)))

            yield frozenset(rule)

    def build_generalisation_constraint3(self, prog, size=None):
        rule = tuple(prog)[0]
        for body in self.find_variants(rule, max_rule_vars=True):
            body = list(body)
            body.append((True, 'body_size', (0, len(body))))
            if size:
                body.append((True, 'program_size_at_least', (size,)))
            yield frozenset(body)

    def build_specialisation_constraint3(self, prog, size=None):
        rule = tuple(prog)[0]
        if not size:
            # print('22222')
            yield from self.find_variants(rule)
            return

        for body in self.find_variants(rule):
            body = list(body)
            body.append((True, 'program_size_at_least', (size,)))
            yield frozenset(body)
    # Leon: find isomorphic rules
    def find_variants(self, rule, max_rule_vars=False):
        head, body = rule
        ## Leon: conditions added, if x is int
        body_vars = frozenset(x for literal in body for x in literal.arguments if is_int(x) and x >= len(head.arguments))
        if max_rule_vars:
            subset = range(len(head.arguments), len(body_vars | set(head.arguments)))
        else:
            subset = range(len(head.arguments), self.settings.max_vars)
        # subset = rang(2,max_vars)
        for xs in permutations(subset, len(body_vars)): # range from the number greater than head arity (the numbers to be taken as body vars)
            xs = head.arguments + xs # 
            new_body = []
            for pred, args in body:
                # if pred == 'att':
                new_args = list()
                # first head_arity of variables of xs are head variables if body_literal is the range of head vars
                # so here only the variables that are above head_arity is changed
                for arg in args:
                    if is_int(arg):
                        new_args.append(xs[arg]) 
                    else:
                        new_args.append(arg)
                new_args = tuple(new_args)
                new_literal = (True, 'body_literal', (0, pred, len(new_args), new_args))
                new_body.append(new_literal)
            yield frozenset(new_body)

    def find_deep_bindings4(self, body):
        head_types = self.settings.head_types
        body_types = self.settings.body_types

        # if no types, find all permutations of variables
        if len(body_types) == 0 or head_types is None:
            num_vars = len({var for atom in body for var in atom.arguments})
            for xs in permutations(range(self.settings.max_vars), num_vars):
                x = {i:xs[i] for i in range(num_vars)}
                yield x
            return

        # if there are types, only find type-safe permutations
        ## lookup for 0,1 are set here
        var_type_lookup = {i:head_type for i, head_type in enumerate(head_types)}

        head_vars = set(range(len(self.settings.head_literal.arguments)))
        body_vars = set()
        
        for pred, args in body:
            for i, x in enumerate(args):
                body_vars.add(x)
                if x in head_vars:
                    continue
                if pred in body_types:
                    var_type_lookup[x] = body_types[pred][i]

        # prohibit bad type matchings
        bad_type_matching = set()
        # Leon: body vars matching with head vars to keep types of vars occur in both head and body consistent
        for x in body_vars:
            if x not in var_type_lookup:
                continue
            for y in head_vars:
                if y not in var_type_lookup:
                    continue
                if var_type_lookup[x] == var_type_lookup[y]:
                    continue
                k = (x, y)
                bad_type_matching.add(k)
        
        lookup = {x:i for i, x in enumerate(body_vars)}
        # len(lookup) number of variables in actual
        for xs in permutations(range(self.settings.max_vars), len(lookup)):
            assignment = {}
            bad = False
            for x in body_vars:
                # xs is a len(lookup)-array vector
                # checking a position on the permutated vector xs 
                # if the pair is identified already as bad type matching
                v = xs[lookup[x]]
                if (x, v) in bad_type_matching:
                    bad = True
                    break
                assignment[x] = v
            if bad:
                continue
            yield assignment
            
    def find_deep_bindings42(self, body):
        head_types = self.settings.head_types
        body_types = self.settings.body_types

        # if no types, find all permutations of variables
        if len(body_types) == 0 or head_types is None:
            num_vars = len({var for atom in body for var in atom.arguments})
            for xs in permutations(range(self.settings.max_vars), num_vars):
                x = {i:xs[i] for i in range(num_vars)}
                yield x
            return

        # if there are types, only find type-safe permutations
        ## lookup for 0,1 are set here
        var_type_lookup = {i:head_type for i, head_type in enumerate(head_types)}

        head_vars = set(range(len(self.settings.head_literal.arguments)))
        body_vars = set()
        
        for pred, args in body:
            for i, x in enumerate(args):
                if is_int(str(x)):
                    body_vars.add(x)
                if x in head_vars:
                    continue
                if pred in body_types:
                    for bt in body_types[pred]:
                        var_type_lookup[x] = [bt[i]] if x not in var_type_lookup else var_type_lookup[x] + [bt[i]]
        var_type_lookup = {k:set(v) for k,v in var_type_lookup.items()}
        # prohibit bad type matchings
        bad_type_matching = set()
        # Leon: body vars matching with head vars to keep types of vars occur in both head and body consistent
        for x in body_vars:
            if x not in var_type_lookup:
                continue
            for y in head_vars:
                if y not in var_type_lookup:
                    continue
                if set(var_type_lookup[x]) == set(var_type_lookup[y]):
                    continue
                k = (x, y)
                bad_type_matching.add(k)
        
        lookup = {x:i for i, x in enumerate(body_vars)}
        # len(lookup) number of variables in actual
        for xs in permutations(range(self.settings.max_vars), len(lookup)):
            assignment = {}
            bad = False
            for x in body_vars:
                # xs is a len(lookup)-array vector
                # checking a position on the permutated vector xs 
                # if the pair is identified already as bad type matching
                v = xs[lookup[x]]
                if (x, v) in bad_type_matching:
                    bad = True
                    break
                assignment[x] = v
            if bad:
                continue
            yield assignment

def remap_variables(rule):
    head, body = rule
    head_vars = set()

    if head:
        head_vars.extend(head.arguments)

    next_var = len(head_vars)
    lookup = {i:i for i in head_vars}

    new_body = set()
    for pred, args in body:
        new_args = []
        for var in args:
            if var not in lookup:
                if is_int(var):
                    lookup[var] = next_var
                    next_var+=1
                else:
                    lookup[var] = var
                # lookup[var] = next_var
                # next_var+=1
            new_args.append(lookup[var])
        new_atom = Literal(pred, tuple(new_args))
        new_body.add(new_atom)

    return head, frozenset(new_body)