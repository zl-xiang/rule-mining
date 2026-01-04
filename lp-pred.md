## Predicates
    ### Bias

Types
Popper supports type annotations in the bias file. A type annotation is of the form `type(p,(t1,t2,...,tk)` for a predicate symbol `p` with arity `k`, such as:

```type(head,(list,element)).
type(tail,(list,list)).
type(length,(list,int,)).
type(empty,(list,)).
type(prepend,(element,list,list)).```

Types are optional but can substantially reduce learning times.

- type(P,Types)/2
    - P: predicates defined in body_pred/2 or head_pred/2
    - Types: a tuple of Types

- type_pos(Types, Pos, Type)/3, EDB, added in `gen2.py`
    - Types:  a tuple of Types
    - Pos: position of a specific type in the tuple
    - Type: name of the type

- var_pos/3, EDB, added in generator
    - var_pos(Var,Vars,Pos)