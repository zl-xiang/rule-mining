()
(0, 1)
%% ##################################################
%% THIS FILE CONTAINS THE ASP PROGRAM GENERATOR, CALLED ALAN
%% ##################################################

#defined direction_/3.
#defined type/2.
#defined non_datalog/0.

#show body_literal/4.

singleton(V):-
    var(V),
    not head_var(_, V),
    #count{P, Vars : body_literal(_, P, _, Vars), var_member(V, Vars)} == 1.

%% max_size(K):-
%%     custom_max_size(K).
max_size(K):-
    max_body(M),
    max_clauses(N),
    K = (M+1)*N.
size(N):-
    max_size(MaxSize),
    N = 2..MaxSize,
    #sum{K+1,Rule : body_size(Rule,K)} == N.

%% THIS DOES NOT WORK!!!???
%% size(N+1):-
%%     body_size(0,N).
:- not size(_).

%% ********** BASE CASE (RULE 0) **********
head_literal(0,P,A,Vars):-
    head_pred(P,A),
    head_vars(A,Vars).

{body_literal(0,P,A,Vars)}:-
    body_pred(P,A),
    vars(A,Vars),
    not bad_body(P,Vars),
    not type_mismatch(P,Vars).

%% Leon may need to check this as well
% TODO: look into the problem here after allowing constants
type_mismatch(P,Vars):-
    var_pos(Var,Vars,Pos),
    type(P,Types),
    pred_arg_type(P,Pos,T1),
    fixed_var_type(Var,T2),
    T1 != T2.

%% THERE IS A CLAUSE IF THERE IS A HEAD LITERAL
clause(C):-
    head_literal(C,_,_,_).

%% NUM BODY LITERALS OF A CLAUSE
%% TODO: IMPROVE AS EXPENSIVE
%% grounding is > c * (n choose k), where n = |Herbrand base| and k = MaxN
body_size(Rule,N):-
    clause(Rule),
    max_body(MaxN),
    N > 0,
    N <= MaxN,
    #count{P,Vars : body_literal(Rule,P,_,Vars)} == N.

%% USE VARS IN ORDER IN A CLAUSE
:-
    clause_var(C,Var1),
    Var1 > 1,
    Var2 = 1..Var1-1,
    not clause_var(C,Var2).

%% POSSIBLE VAR
var(0..N-1):-
    max_vars(N).

%% CLAUSE VAR
clause_var(C,Var):-
    head_var(C,Var).

clause_var(C,Var):-
    body_var(C,Var).

%% HEAD VAR
head_var(C,Var):-
    head_literal(C,_,_,Vars),
    var_member(Var,Vars).

%% BODY VAR
body_var(C,Var):-
    body_literal(C,P,A,Vars),
    % var_member(Var,Vars), 
    var_pos(Var,Vars,Pos), not const(A,Pos).

%% VAR IN A TUPLE OF VARS
var_member(Var,Vars):-
    var_pos(Var,Vars,_).

%% ##################################################
%% BIAS CONSTRAINTS
%% ##################################################
%% DATALOG
%% violated %%
:-
    not non_datalog,
    head_var(Rule,Var),
    not body_var(Rule,Var).

%% if non_datalog is true, all vars are valid
%% constraints used by bk cons
valid_var(Rule,Var):-
    non_datalog,
    Rule=0..MaxRules-1,
    max_clauses(MaxRules),
    var(Var).

%% if datalog, a body only variable is valid
valid_var(Rule,Var):-
    not non_datalog,
    Rule=0..MaxRules-1,
    max_clauses(MaxRules),
    var(Var),
    not head_var(Rule, Var).

%% if datalog, a head var must also appear in the body
valid_var(Rule,Var):-
    not non_datalog,
    head_var(Rule,Var),
    body_var(Rule,Var).

%% MUST BE CONNECTED
%%%%%%%%%% Leon ER rule connectivity %%%%%%%%%%%%
% A tuple variable Tid is connected if it occurs in head
% The rule says a tuple variable Tid is connected in rule R
% if for a variable Var occurs in head of some object rule,
% and Var also occurs the in associated attribute body literal of Tid in the rule R
% For object
t_connected(R,Tid):-
    head_var(R,Var), head_literal(R,eqo,_,Hvars),
    var_member(Var,Hvars), body_literal(R,att,_,Bvars),  var_pos(Var, Bvars, 2), var_pos(Tid, Bvars, 0).

% For value
t_connected(R,Tid):-
    head_var(R,Tid), head_literal(R,eqv,_,Hvars), var_member(Tid,Hvars), 
    body_literal(R,att,_,Bvars), var_pos(Tid, Bvars, 0).

% Similarity join
t_connected(R,Tid):-
    body_literal(R,att,_,Bvars), var_pos(Var, Bvars, 2),
    var_pos(Tid, Bvars, 0), t_connected(R,Tid1), 
    body_literal(R,sim,_,Svars), var_member(Var,Svars), var_member(Var1,Svars), 
    body_literal(R,att,_,Bvars1), var_pos(Tid1, Bvars1, 0), var_pos(Var1, Bvars1, 2).

% Equality join
t_connected(R,Tid):-
    body_literal(R,att,_,Bvars), var_pos(Var, Bvars, 2),
    var_pos(Tid, Bvars, 0), t_connected(R,Tid1), 
    body_literal(R,att,_,Bvars1), var_pos(Tid1, Bvars1, 0), var_pos(Var, Bvars1, 2), Tid != Tid1.

:- body_literal(R,att,_,Bvars), var_pos(Tid,Bvars,0), not t_connected(R,Tid).

%%%%%%%%%% ER rule mining connectivity %%%%%%%%%%%%

head_connected(C,Var):-
    head_var(C,Var).
head_connected(C,Var1):-
    head_literal(C,_,A,_),
    Var1 >= A,
    head_connected(C,Var2),
    body_literal(C,_,_,Vars),
    var_member(Var1,Vars),
    var_member(Var2,Vars),
    Var1 != Var2.

%% violated %%
:-
    head_literal(C,_,A,_),
    Var >= A,
    body_var(C,Var),
    not head_connected(C,Var).

% fixing type of variable Var to Type when it occurs on head
fixed_var_type(Var, Type):-
    head_literal(_, P, _A, Vars),
    var_pos(Var, Vars, Pos),
    type(P, Types),
    %% head_vars(A, Vars),
    type_pos(Types, Pos, Type).

pred_arg_type(P, Pos, Type):-
    type(P, Types),
    type_pos(Types, Pos, Type).

var_type(C, Var, Type):-
    body_literal(C,P,_,Vars),
    var_pos(Var,Vars,Pos),
    type(P,Types),
    type_pos(Types, Pos, Type).

var_type(C, Var, Type):-
    head_literal(C,P,_,Vars),
    var_pos(Var,Vars,Pos),
    type(P,Types),
    type_pos(Types, Pos, Type).


%%% Leon: original code below, commented to allow multiple types for each pred %%%
%%% Could potentially look through bias file and get a maximal number of var types allowed? %%%
%%% e.g. :- clause_var(C,Var), #count{Type : var_type(C,Var,Type)} > {max_type_num}.
%:-
 %   clause_var(C,Var),
  %  #count{Type : var_type(C,Var,Type)} > 1.

deffo_safe(Rule, Var):-
    head_literal(Rule,P,_,Vars),
    var_pos(Var,Vars,Pos),
    direction_(P,Pos,in),
    Rule = 0.

%% VAR SAFE IF HEAD INPUT VAR
safe_bvar(Rule,Var):-
    head_literal(Rule,P,_,Vars),
    var_pos(Var,Vars,Pos),
    direction_(P,Pos,in).

%% VAR SAFE IF A OUTPUT VAR
safe_bvar(Rule,Var):-
    direction_(_,_,_),
    not deffo_safe(Rule, Var),
    body_literal(Rule,P,_,Vars),
    #count{Pos : direction_(P,Pos,in)} == 0,
    var_member(Var,Vars).

%% VAR SAFE IF ALL INPUT VARS ARE SAFE
safe_bvar(Rule,Var):-
    not deffo_safe(Rule, Var),
    body_literal(Rule, P, _, Vars),
    var_member(Var, Vars),
    #count{Pos : direction_(P,Pos,in)} > 0,
    safe_bvar(Rule,Var2) : var_pos(Var2,Vars,Pos), direction_(P,Pos,in).

:-
    direction_(_,_,_),
    body_var(Rule,Var),
    not safe_bvar(Rule,Var).

%% %% ==========================================================================================
%% %% BK BIAS CONSTRAINTS
%% %% ==========================================================================================
%% IDEAS FROM THE PAPER:
%% Learning logic programs by discovering where not to search. A. Cropper and C. Hocquette. AAAI23.

bad_body(P, Vars):- prop(ab_ba,(P,P)), vars(_, Vars), Vars=(A,B), A>B.
bad_body(P, Vars):- prop(ab_ba,(P,P)), vars(_, Vars), Vars=(A,B), A>B.
bad_body(P, Vars):- prop(abc_acb,(P,P)), vars(_, Vars), Vars=(A,B,C), B>C.
bad_body(P, Vars):- prop(abc_bac,(P,P)), vars(_, Vars), Vars=(A,B,C), A>B.
bad_body(P, Vars):- prop(abc_cba,(P,P)), vars(_, Vars), Vars=(A,B,C), A>C.
bad_body(P, Vars):- prop(abcd_abdc,(P,P)), vars(_, Vars), Vars=(A,B,C,D), C>D.
bad_body(P, Vars):- prop(abcd_acbd,(P,P)), vars(_, Vars), Vars=(A,B,C,D), B>C.
bad_body(P, Vars):- prop(abcd_adcb,(P,P)), vars(_, Vars), Vars=(A,B,C,D), B>D.
bad_body(P, Vars):- prop(abcd_bacd,(P,P)), vars(_, Vars), Vars=(A,B,C,D), A>B.
bad_body(P, Vars):- prop(abcd_badc,(P,P)), vars(_, Vars), Vars=(A,B,C,D), A>B.
bad_body(P, Vars):- prop(abcd_cbad,(P,P)), vars(_, Vars), Vars=(A,B,C,D), A>C.
bad_body(P, Vars):- prop(abcd_cdab,(P,P)), vars(_, Vars), Vars=(A,B,C,D), A>C.
bad_body(P, Vars):- prop(abcd_dbca,(P,P)), vars(_, Vars), Vars=(A,B,C,D), A>D.
bad_body(P, Vars):- prop(abcd_dcba,(P,P)), vars(_, Vars), Vars=(A,B,C,D), B>C.
bad_body(P, Vars):- prop(abcde_abced,(P,P)), vars(_, Vars), Vars=(A,B,C,D,E), D>E.
bad_body(P, Vars):- prop(abcde_abdce,(P,P)), vars(_, Vars), Vars=(A,B,C,D,E), C>D.
bad_body(P, Vars):- prop(abcde_abedc,(P,P)), vars(_, Vars), Vars=(A,B,C,D,E), C>E.
bad_body(P, Vars):- prop(abcde_acbde,(P,P)), vars(_, Vars), Vars=(A,B,C,D,E), B>C.
bad_body(P, Vars):- prop(abcde_acbed,(P,P)), vars(_, Vars), Vars=(A,B,C,D,E), B>C.
bad_body(P, Vars):- prop(abcde_adcbe,(P,P)), vars(_, Vars), Vars=(A,B,C,D,E), B>D.
bad_body(P, Vars):- prop(abcde_adebc,(P,P)), vars(_, Vars), Vars=(A,B,C,D,E), B>D.
bad_body(P, Vars):- prop(abcde_aecdb,(P,P)), vars(_, Vars), Vars=(A,B,C,D,E), B>E.
bad_body(P, Vars):- prop(abcde_aedcb,(P,P)), vars(_, Vars), Vars=(A,B,C,D,E), C>D.
bad_body(P, Vars):- prop(abcde_bacde,(P,P)), vars(_, Vars), Vars=(A,B,C,D,E), A>B.
bad_body(P, Vars):- prop(abcde_baced,(P,P)), vars(_, Vars), Vars=(A,B,C,D,E), A>B.
bad_body(P, Vars):- prop(abcde_badce,(P,P)), vars(_, Vars), Vars=(A,B,C,D,E), A>B.
bad_body(P, Vars):- prop(abcde_badec,(P,P)), vars(_, Vars), Vars=(A,B,C,D,E), A>B.
bad_body(P, Vars):- prop(abcde_baedc,(P,P)), vars(_, Vars), Vars=(A,B,C,D,E), A>B.
bad_body(P, Vars):- prop(abcde_bcaed,(P,P)), vars(_, Vars), Vars=(A,B,C,D,E), D>E.
bad_body(P, Vars):- prop(abcde_bdeac,(P,P)), vars(_, Vars), Vars=(A,B,C,D,E), C>E.
bad_body(P, Vars):- prop(abcde_bedca,(P,P)), vars(_, Vars), Vars=(A,B,C,D,E), C>D.
bad_body(P, Vars):- prop(abcde_cbade,(P,P)), vars(_, Vars), Vars=(A,B,C,D,E), A>C.
bad_body(P, Vars):- prop(abcde_cbaed,(P,P)), vars(_, Vars), Vars=(A,B,C,D,E), A>C.
bad_body(P, Vars):- prop(abcde_cdabe,(P,P)), vars(_, Vars), Vars=(A,B,C,D,E), A>C.
bad_body(P, Vars):- prop(abcde_cdaeb,(P,P)), vars(_, Vars), Vars=(A,B,C,D,E), A>C.
bad_body(P, Vars):- prop(abcde_cdeba,(P,P)), vars(_, Vars), Vars=(A,B,C,D,E), B>D.
bad_body(P, Vars):- prop(abcde_ceadb,(P,P)), vars(_, Vars), Vars=(A,B,C,D,E), A>C.
bad_body(P, Vars):- prop(abcde_cedab,(P,P)), vars(_, Vars), Vars=(A,B,C,D,E), B>E.
bad_body(P, Vars):- prop(abcde_dbcae,(P,P)), vars(_, Vars), Vars=(A,B,C,D,E), A>D.
bad_body(P, Vars):- prop(abcde_dbeac,(P,P)), vars(_, Vars), Vars=(A,B,C,D,E), A>D.
bad_body(P, Vars):- prop(abcde_dcbae,(P,P)), vars(_, Vars), Vars=(A,B,C,D,E), B>C.
bad_body(P, Vars):- prop(abcde_dcbea,(P,P)), vars(_, Vars), Vars=(A,B,C,D,E), B>C.
bad_body(P, Vars):- prop(abcde_dceab,(P,P)), vars(_, Vars), Vars=(A,B,C,D,E), A>D.
bad_body(P, Vars):- prop(abcde_decab,(P,P)), vars(_, Vars), Vars=(A,B,C,D,E), A>D.
bad_body(P, Vars):- prop(abcde_ebcda,(P,P)), vars(_, Vars), Vars=(A,B,C,D,E), A>E.
bad_body(P, Vars):- prop(abcde_ebdca,(P,P)), vars(_, Vars), Vars=(A,B,C,D,E), C>D.
bad_body(P, Vars):- prop(abcde_ecbda,(P,P)), vars(_, Vars), Vars=(A,B,C,D,E), B>C.
bad_body(P, Vars):- prop(abcde_ecdba,(P,P)), vars(_, Vars), Vars=(A,B,C,D,E), A>E.
bad_body(P, Vars):- prop(abcde_edcba,(P,P)), vars(_, Vars), Vars=(A,B,C,D,E), B>D.
bad_body(P, Vars):- prop(abcdef_abcdfe,(P,P)), vars(_, Vars), Vars=(A,B,C,D,E,F), E>F.
bad_body(P, Vars):- prop(abcdef_abcedf,(P,P)), vars(_, Vars), Vars=(A,B,C,D,E,F), D>E.
bad_body(P, Vars):- prop(abcdef_abcfed,(P,P)), vars(_, Vars), Vars=(A,B,C,D,E,F), D>F.
bad_body(P, Vars):- prop(abcdef_abdcef,(P,P)), vars(_, Vars), Vars=(A,B,C,D,E,F), C>D.
bad_body(P, Vars):- prop(abcdef_abdcfe,(P,P)), vars(_, Vars), Vars=(A,B,C,D,E,F), C>D.
bad_body(P, Vars):- prop(abcdef_abedcf,(P,P)), vars(_, Vars), Vars=(A,B,C,D,E,F), C>E.
bad_body(P, Vars):- prop(abcdef_abefcd,(P,P)), vars(_, Vars), Vars=(A,B,C,D,E,F), C>E.
bad_body(P, Vars):- prop(abcdef_abfdec,(P,P)), vars(_, Vars), Vars=(A,B,C,D,E,F), C>F.
bad_body(P, Vars):- prop(abcdef_abfedc,(P,P)), vars(_, Vars), Vars=(A,B,C,D,E,F), D>E.
bad_body(P, Vars):- prop(abcdef_acbdef,(P,P)), vars(_, Vars), Vars=(A,B,C,D,E,F), B>C.
bad_body(P, Vars):- prop(abcdef_acbdfe,(P,P)), vars(_, Vars), Vars=(A,B,C,D,E,F), B>C.
bad_body(P, Vars):- prop(abcdef_acbedf,(P,P)), vars(_, Vars), Vars=(A,B,C,D,E,F), B>C.
bad_body(P, Vars):- prop(abcdef_acbefd,(P,P)), vars(_, Vars), Vars=(A,B,C,D,E,F), B>C.
bad_body(P, Vars):- prop(abcdef_acbfed,(P,P)), vars(_, Vars), Vars=(A,B,C,D,E,F), B>C.
bad_body(P, Vars):- prop(abcdef_acdbfe,(P,P)), vars(_, Vars), Vars=(A,B,C,D,E,F), E>F.
bad_body(P, Vars):- prop(abcdef_acefbd,(P,P)), vars(_, Vars), Vars=(A,B,C,D,E,F), D>F.
bad_body(P, Vars):- prop(abcdef_acfedb,(P,P)), vars(_, Vars), Vars=(A,B,C,D,E,F), D>E.
bad_body(P, Vars):- prop(abcdef_adcbef,(P,P)), vars(_, Vars), Vars=(A,B,C,D,E,F), B>D.
bad_body(P, Vars):- prop(abcdef_adcbfe,(P,P)), vars(_, Vars), Vars=(A,B,C,D,E,F), B>D.
bad_body(P, Vars):- prop(abcdef_adebcf,(P,P)), vars(_, Vars), Vars=(A,B,C,D,E,F), B>D.
bad_body(P, Vars):- prop(abcdef_adebfc,(P,P)), vars(_, Vars), Vars=(A,B,C,D,E,F), B>D.
bad_body(P, Vars):- prop(abcdef_adefcb,(P,P)), vars(_, Vars), Vars=(A,B,C,D,E,F), C>E.
bad_body(P, Vars):- prop(abcdef_adfbec,(P,P)), vars(_, Vars), Vars=(A,B,C,D,E,F), B>D.
bad_body(P, Vars):- prop(abcdef_adfebc,(P,P)), vars(_, Vars), Vars=(A,B,C,D,E,F), C>F.
bad_body(P, Vars):- prop(abcdef_aecdbf,(P,P)), vars(_, Vars), Vars=(A,B,C,D,E,F), B>E.
bad_body(P, Vars):- prop(abcdef_aecfbd,(P,P)), vars(_, Vars), Vars=(A,B,C,D,E,F), B>E.
bad_body(P, Vars):- prop(abcdef_aedcbf,(P,P)), vars(_, Vars), Vars=(A,B,C,D,E,F), C>D.
bad_body(P, Vars):- prop(abcdef_aedcfb,(P,P)), vars(_, Vars), Vars=(A,B,C,D,E,F), C>D.
bad_body(P, Vars):- prop(abcdef_aedfbc,(P,P)), vars(_, Vars), Vars=(A,B,C,D,E,F), B>E.
bad_body(P, Vars):- prop(abcdef_aefdbc,(P,P)), vars(_, Vars), Vars=(A,B,C,D,E,F), B>E.
bad_body(P, Vars):- prop(abcdef_afcdeb,(P,P)), vars(_, Vars), Vars=(A,B,C,D,E,F), B>F.
bad_body(P, Vars):- prop(abcdef_afcedb,(P,P)), vars(_, Vars), Vars=(A,B,C,D,E,F), D>E.
bad_body(P, Vars):- prop(abcdef_afdceb,(P,P)), vars(_, Vars), Vars=(A,B,C,D,E,F), C>D.
bad_body(P, Vars):- prop(abcdef_afdecb,(P,P)), vars(_, Vars), Vars=(A,B,C,D,E,F), B>F.
bad_body(P, Vars):- prop(abcdef_afedcb,(P,P)), vars(_, Vars), Vars=(A,B,C,D,E,F), C>E.
bad_body(P, Vars):- prop(abcdef_bacdef,(P,P)), vars(_, Vars), Vars=(A,B,C,D,E,F), A>B.
bad_body(P, Vars):- prop(abcdef_bacdfe,(P,P)), vars(_, Vars), Vars=(A,B,C,D,E,F), A>B.
bad_body(P, Vars):- prop(abcdef_bacedf,(P,P)), vars(_, Vars), Vars=(A,B,C,D,E,F), A>B.
bad_body(P, Vars):- prop(abcdef_bacefd,(P,P)), vars(_, Vars), Vars=(A,B,C,D,E,F), A>B.
bad_body(P, Vars):- prop(abcdef_bacfed,(P,P)), vars(_, Vars), Vars=(A,B,C,D,E,F), A>B.
bad_body(P, Vars):- prop(abcdef_badcef,(P,P)), vars(_, Vars), Vars=(A,B,C,D,E,F), A>B.
bad_body(P, Vars):- prop(abcdef_badcfe,(P,P)), vars(_, Vars), Vars=(A,B,C,D,E,F), A>B.
bad_body(P, Vars):- prop(abcdef_badecf,(P,P)), vars(_, Vars), Vars=(A,B,C,D,E,F), A>B.
bad_body(P, Vars):- prop(abcdef_badefc,(P,P)), vars(_, Vars), Vars=(A,B,C,D,E,F), A>B.
bad_body(P, Vars):- prop(abcdef_badfce,(P,P)), vars(_, Vars), Vars=(A,B,C,D,E,F), A>B.
bad_body(P, Vars):- prop(abcdef_badfec,(P,P)), vars(_, Vars), Vars=(A,B,C,D,E,F), A>B.
bad_body(P, Vars):- prop(abcdef_baedcf,(P,P)), vars(_, Vars), Vars=(A,B,C,D,E,F), A>B.
bad_body(P, Vars):- prop(abcdef_baedfc,(P,P)), vars(_, Vars), Vars=(A,B,C,D,E,F), A>B.
bad_body(P, Vars):- prop(abcdef_baefcd,(P,P)), vars(_, Vars), Vars=(A,B,C,D,E,F), A>B.
bad_body(P, Vars):- prop(abcdef_baefdc,(P,P)), vars(_, Vars), Vars=(A,B,C,D,E,F), A>B.
bad_body(P, Vars):- prop(abcdef_bafdec,(P,P)), vars(_, Vars), Vars=(A,B,C,D,E,F), A>B.
bad_body(P, Vars):- prop(abcdef_bafedc,(P,P)), vars(_, Vars), Vars=(A,B,C,D,E,F), A>B.
bad_body(P, Vars):- prop(abcdef_bcadfe,(P,P)), vars(_, Vars), Vars=(A,B,C,D,E,F), E>F.
bad_body(P, Vars):- prop(abcdef_bcaedf,(P,P)), vars(_, Vars), Vars=(A,B,C,D,E,F), D>E.
bad_body(P, Vars):- prop(abcdef_bcafed,(P,P)), vars(_, Vars), Vars=(A,B,C,D,E,F), D>F.
bad_body(P, Vars):- prop(abcdef_bcdafe,(P,P)), vars(_, Vars), Vars=(A,B,C,D,E,F), E>F.
bad_body(P, Vars):- prop(abcdef_bcefad,(P,P)), vars(_, Vars), Vars=(A,B,C,D,E,F), D>F.
bad_body(P, Vars):- prop(abcdef_bcfeda,(P,P)), vars(_, Vars), Vars=(A,B,C,D,E,F), D>E.
bad_body(P, Vars):- prop(abcdef_bdacfe,(P,P)), vars(_, Vars), Vars=(A,B,C,D,E,F), E>F.
bad_body(P, Vars):- prop(abcdef_bdcafe,(P,P)), vars(_, Vars), Vars=(A,B,C,D,E,F), E>F.
bad_body(P, Vars):- prop(abcdef_bdeacf,(P,P)), vars(_, Vars), Vars=(A,B,C,D,E,F), C>E.
bad_body(P, Vars):- prop(abcdef_bdefca,(P,P)), vars(_, Vars), Vars=(A,B,C,D,E,F), C>E.
bad_body(P, Vars):- prop(abcdef_bdfaec,(P,P)), vars(_, Vars), Vars=(A,B,C,D,E,F), C>F.
bad_body(P, Vars):- prop(abcdef_bdfeac,(P,P)), vars(_, Vars), Vars=(A,B,C,D,E,F), C>F.
bad_body(P, Vars):- prop(abcdef_beafcd,(P,P)), vars(_, Vars), Vars=(A,B,C,D,E,F), D>F.
bad_body(P, Vars):- prop(abcdef_becfad,(P,P)), vars(_, Vars), Vars=(A,B,C,D,E,F), D>F.
bad_body(P, Vars):- prop(abcdef_bedcaf,(P,P)), vars(_, Vars), Vars=(A,B,C,D,E,F), C>D.
bad_body(P, Vars):- prop(abcdef_bedcfa,(P,P)), vars(_, Vars), Vars=(A,B,C,D,E,F), C>D.
bad_body(P, Vars):- prop(abcdef_befadc,(P,P)), vars(_, Vars), Vars=(A,B,C,D,E,F), C>F.
bad_body(P, Vars):- prop(abcdef_befdac,(P,P)), vars(_, Vars), Vars=(A,B,C,D,E,F), C>F.
bad_body(P, Vars):- prop(abcdef_bfaedc,(P,P)), vars(_, Vars), Vars=(A,B,C,D,E,F), D>E.
bad_body(P, Vars):- prop(abcdef_bfceda,(P,P)), vars(_, Vars), Vars=(A,B,C,D,E,F), D>E.
bad_body(P, Vars):- prop(abcdef_bfdcae,(P,P)), vars(_, Vars), Vars=(A,B,C,D,E,F), C>D.
bad_body(P, Vars):- prop(abcdef_bfdcea,(P,P)), vars(_, Vars), Vars=(A,B,C,D,E,F), C>D.
bad_body(P, Vars):- prop(abcdef_bfeacd,(P,P)), vars(_, Vars), Vars=(A,B,C,D,E,F), C>E.
bad_body(P, Vars):- prop(abcdef_bfedca,(P,P)), vars(_, Vars), Vars=(A,B,C,D,E,F), C>E.
bad_body(P, Vars):- prop(abcdef_cbadef,(P,P)), vars(_, Vars), Vars=(A,B,C,D,E,F), A>C.
bad_body(P, Vars):- prop(abcdef_cbadfe,(P,P)), vars(_, Vars), Vars=(A,B,C,D,E,F), A>C.
bad_body(P, Vars):- prop(abcdef_cbaedf,(P,P)), vars(_, Vars), Vars=(A,B,C,D,E,F), A>C.
bad_body(P, Vars):- prop(abcdef_cbaefd,(P,P)), vars(_, Vars), Vars=(A,B,C,D,E,F), A>C.
bad_body(P, Vars):- prop(abcdef_cbafed,(P,P)), vars(_, Vars), Vars=(A,B,C,D,E,F), A>C.
bad_body(P, Vars):- prop(abcdef_cbdafe,(P,P)), vars(_, Vars), Vars=(A,B,C,D,E,F), E>F.
bad_body(P, Vars):- prop(abcdef_cbefad,(P,P)), vars(_, Vars), Vars=(A,B,C,D,E,F), D>F.
bad_body(P, Vars):- prop(abcdef_cbfeda,(P,P)), vars(_, Vars), Vars=(A,B,C,D,E,F), D>E.
bad_body(P, Vars):- prop(abcdef_cdabef,(P,P)), vars(_, Vars), Vars=(A,B,C,D,E,F), A>C.
bad_body(P, Vars):- prop(abcdef_cdabfe,(P,P)), vars(_, Vars), Vars=(A,B,C,D,E,F), A>C.
bad_body(P, Vars):- prop(abcdef_cdaebf,(P,P)), vars(_, Vars), Vars=(A,B,C,D,E,F), A>C.
bad_body(P, Vars):- prop(abcdef_cdaefb,(P,P)), vars(_, Vars), Vars=(A,B,C,D,E,F), A>C.
bad_body(P, Vars):- prop(abcdef_cdafbe,(P,P)), vars(_, Vars), Vars=(A,B,C,D,E,F), A>C.
bad_body(P, Vars):- prop(abcdef_cdafeb,(P,P)), vars(_, Vars), Vars=(A,B,C,D,E,F), A>C.
bad_body(P, Vars):- prop(abcdef_cdbafe,(P,P)), vars(_, Vars), Vars=(A,B,C,D,E,F), E>F.
bad_body(P, Vars):- prop(abcdef_cdebaf,(P,P)), vars(_, Vars), Vars=(A,B,C,D,E,F), B>D.
bad_body(P, Vars):- prop(abcdef_cdebfa,(P,P)), vars(_, Vars), Vars=(A,B,C,D,E,F), B>D.
bad_body(P, Vars):- prop(abcdef_cdfbae,(P,P)), vars(_, Vars), Vars=(A,B,C,D,E,F), B>D.
bad_body(P, Vars):- prop(abcdef_cdfbea,(P,P)), vars(_, Vars), Vars=(A,B,C,D,E,F), B>D.
bad_body(P, Vars):- prop(abcdef_ceadbf,(P,P)), vars(_, Vars), Vars=(A,B,C,D,E,F), A>C.
bad_body(P, Vars):- prop(abcdef_ceadfb,(P,P)), vars(_, Vars), Vars=(A,B,C,D,E,F), A>C.
bad_body(P, Vars):- prop(abcdef_ceafbd,(P,P)), vars(_, Vars), Vars=(A,B,C,D,E,F), A>C.
bad_body(P, Vars):- prop(abcdef_ceafdb,(P,P)), vars(_, Vars), Vars=(A,B,C,D,E,F), A>C.
bad_body(P, Vars):- prop(abcdef_cebfad,(P,P)), vars(_, Vars), Vars=(A,B,C,D,E,F), D>F.
bad_body(P, Vars):- prop(abcdef_cedabf,(P,P)), vars(_, Vars), Vars=(A,B,C,D,E,F), B>E.
bad_body(P, Vars):- prop(abcdef_cedfba,(P,P)), vars(_, Vars), Vars=(A,B,C,D,E,F), B>E.
bad_body(P, Vars):- prop(abcdef_cefabd,(P,P)), vars(_, Vars), Vars=(A,B,C,D,E,F), B>E.
bad_body(P, Vars):- prop(abcdef_cefdba,(P,P)), vars(_, Vars), Vars=(A,B,C,D,E,F), B>E.
bad_body(P, Vars):- prop(abcdef_cfadeb,(P,P)), vars(_, Vars), Vars=(A,B,C,D,E,F), A>C.
bad_body(P, Vars):- prop(abcdef_cfaedb,(P,P)), vars(_, Vars), Vars=(A,B,C,D,E,F), A>C.
bad_body(P, Vars):- prop(abcdef_cfbeda,(P,P)), vars(_, Vars), Vars=(A,B,C,D,E,F), D>E.
bad_body(P, Vars):- prop(abcdef_cfdaeb,(P,P)), vars(_, Vars), Vars=(A,B,C,D,E,F), B>F.
bad_body(P, Vars):- prop(abcdef_cfdeab,(P,P)), vars(_, Vars), Vars=(A,B,C,D,E,F), B>F.
bad_body(P, Vars):- prop(abcdef_cfeadb,(P,P)), vars(_, Vars), Vars=(A,B,C,D,E,F), B>F.
bad_body(P, Vars):- prop(abcdef_cfedab,(P,P)), vars(_, Vars), Vars=(A,B,C,D,E,F), B>F.
bad_body(P, Vars):- prop(abcdef_dbcaef,(P,P)), vars(_, Vars), Vars=(A,B,C,D,E,F), A>D.
bad_body(P, Vars):- prop(abcdef_dbcafe,(P,P)), vars(_, Vars), Vars=(A,B,C,D,E,F), A>D.
bad_body(P, Vars):- prop(abcdef_dbeacf,(P,P)), vars(_, Vars), Vars=(A,B,C,D,E,F), A>D.
bad_body(P, Vars):- prop(abcdef_dbeafc,(P,P)), vars(_, Vars), Vars=(A,B,C,D,E,F), A>D.
bad_body(P, Vars):- prop(abcdef_dbefca,(P,P)), vars(_, Vars), Vars=(A,B,C,D,E,F), C>E.
bad_body(P, Vars):- prop(abcdef_dbfaec,(P,P)), vars(_, Vars), Vars=(A,B,C,D,E,F), A>D.
bad_body(P, Vars):- prop(abcdef_dbfeac,(P,P)), vars(_, Vars), Vars=(A,B,C,D,E,F), C>F.
bad_body(P, Vars):- prop(abcdef_dcbaef,(P,P)), vars(_, Vars), Vars=(A,B,C,D,E,F), B>C.
bad_body(P, Vars):- prop(abcdef_dcbafe,(P,P)), vars(_, Vars), Vars=(A,B,C,D,E,F), B>C.
bad_body(P, Vars):- prop(abcdef_dcbeaf,(P,P)), vars(_, Vars), Vars=(A,B,C,D,E,F), B>C.
bad_body(P, Vars):- prop(abcdef_dcbefa,(P,P)), vars(_, Vars), Vars=(A,B,C,D,E,F), B>C.
bad_body(P, Vars):- prop(abcdef_dcbfae,(P,P)), vars(_, Vars), Vars=(A,B,C,D,E,F), B>C.
bad_body(P, Vars):- prop(abcdef_dcbfea,(P,P)), vars(_, Vars), Vars=(A,B,C,D,E,F), B>C.
bad_body(P, Vars):- prop(abcdef_dceabf,(P,P)), vars(_, Vars), Vars=(A,B,C,D,E,F), A>D.
bad_body(P, Vars):- prop(abcdef_dceafb,(P,P)), vars(_, Vars), Vars=(A,B,C,D,E,F), A>D.
bad_body(P, Vars):- prop(abcdef_dcfabe,(P,P)), vars(_, Vars), Vars=(A,B,C,D,E,F), A>D.
bad_body(P, Vars):- prop(abcdef_dcfaeb,(P,P)), vars(_, Vars), Vars=(A,B,C,D,E,F), A>D.
bad_body(P, Vars):- prop(abcdef_decabf,(P,P)), vars(_, Vars), Vars=(A,B,C,D,E,F), A>D.
bad_body(P, Vars):- prop(abcdef_decafb,(P,P)), vars(_, Vars), Vars=(A,B,C,D,E,F), A>D.
bad_body(P, Vars):- prop(abcdef_decfba,(P,P)), vars(_, Vars), Vars=(A,B,C,D,E,F), B>E.
bad_body(P, Vars):- prop(abcdef_defabc,(P,P)), vars(_, Vars), Vars=(A,B,C,D,E,F), A>D.
bad_body(P, Vars):- prop(abcdef_defacb,(P,P)), vars(_, Vars), Vars=(A,B,C,D,E,F), A>D.
bad_body(P, Vars):- prop(abcdef_defbac,(P,P)), vars(_, Vars), Vars=(A,B,C,D,E,F), C>F.
bad_body(P, Vars):- prop(abcdef_defcba,(P,P)), vars(_, Vars), Vars=(A,B,C,D,E,F), B>E.
bad_body(P, Vars):- prop(abcdef_dfcaeb,(P,P)), vars(_, Vars), Vars=(A,B,C,D,E,F), A>D.
bad_body(P, Vars):- prop(abcdef_dfceab,(P,P)), vars(_, Vars), Vars=(A,B,C,D,E,F), B>F.
bad_body(P, Vars):- prop(abcdef_dfeacb,(P,P)), vars(_, Vars), Vars=(A,B,C,D,E,F), A>D.
bad_body(P, Vars):- prop(abcdef_dfebca,(P,P)), vars(_, Vars), Vars=(A,B,C,D,E,F), C>E.
bad_body(P, Vars):- prop(abcdef_dfecab,(P,P)), vars(_, Vars), Vars=(A,B,C,D,E,F), B>F.
bad_body(P, Vars):- prop(abcdef_ebcdaf,(P,P)), vars(_, Vars), Vars=(A,B,C,D,E,F), A>E.
bad_body(P, Vars):- prop(abcdef_ebcfad,(P,P)), vars(_, Vars), Vars=(A,B,C,D,E,F), A>E.
bad_body(P, Vars):- prop(abcdef_ebdcaf,(P,P)), vars(_, Vars), Vars=(A,B,C,D,E,F), C>D.
bad_body(P, Vars):- prop(abcdef_ebdcfa,(P,P)), vars(_, Vars), Vars=(A,B,C,D,E,F), C>D.
bad_body(P, Vars):- prop(abcdef_ebdfac,(P,P)), vars(_, Vars), Vars=(A,B,C,D,E,F), A>E.
bad_body(P, Vars):- prop(abcdef_ebfdac,(P,P)), vars(_, Vars), Vars=(A,B,C,D,E,F), A>E.
bad_body(P, Vars):- prop(abcdef_ecbdaf,(P,P)), vars(_, Vars), Vars=(A,B,C,D,E,F), B>C.
bad_body(P, Vars):- prop(abcdef_ecbdfa,(P,P)), vars(_, Vars), Vars=(A,B,C,D,E,F), B>C.
bad_body(P, Vars):- prop(abcdef_ecbfad,(P,P)), vars(_, Vars), Vars=(A,B,C,D,E,F), B>C.
bad_body(P, Vars):- prop(abcdef_ecbfda,(P,P)), vars(_, Vars), Vars=(A,B,C,D,E,F), B>C.
bad_body(P, Vars):- prop(abcdef_ecdbaf,(P,P)), vars(_, Vars), Vars=(A,B,C,D,E,F), A>E.
bad_body(P, Vars):- prop(abcdef_ecdfab,(P,P)), vars(_, Vars), Vars=(A,B,C,D,E,F), A>E.
bad_body(P, Vars):- prop(abcdef_ecfbad,(P,P)), vars(_, Vars), Vars=(A,B,C,D,E,F), A>E.
bad_body(P, Vars):- prop(abcdef_ecfdab,(P,P)), vars(_, Vars), Vars=(A,B,C,D,E,F), A>E.
bad_body(P, Vars):- prop(abcdef_edcbaf,(P,P)), vars(_, Vars), Vars=(A,B,C,D,E,F), B>D.
bad_body(P, Vars):- prop(abcdef_edcbfa,(P,P)), vars(_, Vars), Vars=(A,B,C,D,E,F), B>D.
bad_body(P, Vars):- prop(abcdef_edcfab,(P,P)), vars(_, Vars), Vars=(A,B,C,D,E,F), A>E.
bad_body(P, Vars):- prop(abcdef_edfbac,(P,P)), vars(_, Vars), Vars=(A,B,C,D,E,F), B>D.
bad_body(P, Vars):- prop(abcdef_edfbca,(P,P)), vars(_, Vars), Vars=(A,B,C,D,E,F), B>D.
bad_body(P, Vars):- prop(abcdef_edfcab,(P,P)), vars(_, Vars), Vars=(A,B,C,D,E,F), A>E.
bad_body(P, Vars):- prop(abcdef_efcdab,(P,P)), vars(_, Vars), Vars=(A,B,C,D,E,F), A>E.
bad_body(P, Vars):- prop(abcdef_efdcab,(P,P)), vars(_, Vars), Vars=(A,B,C,D,E,F), C>D.
bad_body(P, Vars):- prop(abcdef_efdcba,(P,P)), vars(_, Vars), Vars=(A,B,C,D,E,F), C>D.
bad_body(P, Vars):- prop(abcdef_fbcdea,(P,P)), vars(_, Vars), Vars=(A,B,C,D,E,F), A>F.
bad_body(P, Vars):- prop(abcdef_fbceda,(P,P)), vars(_, Vars), Vars=(A,B,C,D,E,F), D>E.
bad_body(P, Vars):- prop(abcdef_fbdcea,(P,P)), vars(_, Vars), Vars=(A,B,C,D,E,F), C>D.
bad_body(P, Vars):- prop(abcdef_fbdeca,(P,P)), vars(_, Vars), Vars=(A,B,C,D,E,F), A>F.
bad_body(P, Vars):- prop(abcdef_fbedca,(P,P)), vars(_, Vars), Vars=(A,B,C,D,E,F), C>E.
bad_body(P, Vars):- prop(abcdef_fcbdea,(P,P)), vars(_, Vars), Vars=(A,B,C,D,E,F), B>C.
bad_body(P, Vars):- prop(abcdef_fcbeda,(P,P)), vars(_, Vars), Vars=(A,B,C,D,E,F), B>C.
bad_body(P, Vars):- prop(abcdef_fcdbea,(P,P)), vars(_, Vars), Vars=(A,B,C,D,E,F), A>F.
bad_body(P, Vars):- prop(abcdef_fcdeba,(P,P)), vars(_, Vars), Vars=(A,B,C,D,E,F), A>F.
bad_body(P, Vars):- prop(abcdef_fcebda,(P,P)), vars(_, Vars), Vars=(A,B,C,D,E,F), A>F.
bad_body(P, Vars):- prop(abcdef_fcedba,(P,P)), vars(_, Vars), Vars=(A,B,C,D,E,F), A>F.
bad_body(P, Vars):- prop(abcdef_fdcbea,(P,P)), vars(_, Vars), Vars=(A,B,C,D,E,F), B>D.
bad_body(P, Vars):- prop(abcdef_fdceba,(P,P)), vars(_, Vars), Vars=(A,B,C,D,E,F), A>F.
bad_body(P, Vars):- prop(abcdef_fdebca,(P,P)), vars(_, Vars), Vars=(A,B,C,D,E,F), B>D.
bad_body(P, Vars):- prop(abcdef_fdecba,(P,P)), vars(_, Vars), Vars=(A,B,C,D,E,F), A>F.
bad_body(P, Vars):- prop(abcdef_fecdba,(P,P)), vars(_, Vars), Vars=(A,B,C,D,E,F), B>E.
bad_body(P, Vars):- prop(abcdef_fedcba,(P,P)), vars(_, Vars), Vars=(A,B,C,D,E,F), C>D.

%% TRY TO REDUCE THE NUMBER OF RULES WITH REDUNDANT LITERALS

:-
    body_literal(_,P,_,(A,B)),
    body_literal(_,P,_,(A,C)),
    B!=C,
    singleton(B).

:-
    body_literal(_,P,_,(B,A)),
    body_literal(_,P,_,(C,A)),
    B!=C,
    singleton(B).

:-
    body_literal(_,P,_,(A,B,X)),
    body_literal(_,P,_,(A,B,Y)),
    X!=Y,
    singleton(X).

:-
    body_literal(_,P,_,(A,X,B)),
    body_literal(_,P,_,(A,Y,B)),
    X!=Y,
    singleton(X).

:-
    body_literal(_,P,_,(A,B,C)),
    body_literal(_,P,_,(A,X,Y)),
    B!=X,
    C!=Y,
    singleton(X),
    singleton(Y).

:-
    body_literal(_,P,_,(B,A,C)),
    body_literal(_,P,_,(X,A,Y)),
    B!=X,
    C!=Y,
    singleton(X).

:-
    body_literal(_,P,_,(B,C,A)),
    body_literal(_,P,_,(X,Y,A)),
    B!=X,
    C!=Y,
    singleton(X).

:-
    body_literal(_,P,_,(X,V0,V1)),
    body_literal(_,P,_,(Y,V0,V1)),
    X!=Y,
    singleton(X).

:-
    body_literal(_,P,_,(V0,V4,V3,V5)),
    body_literal(_,P,_,(V0,V2,V3,V1)),
    V4!=V2,
    V5!=V1,
    singleton(V2),
    singleton(V1).

:-
    body_literal(_,P,_,(V0,V1,V2,X)),
    body_literal(_,P,_,(V0,V1,V2,Y)),
    X!=Y,
    singleton(Y).

:-
    body_literal(_,P,_,(V0,V3,V4,V1)),
    body_literal(_,P,_,(V0,V2,V4,V1)),
    V3!=V2,
    singleton(V3).

:-
    body_literal(_,P,_,(V0,V4,V3,V1)),
    body_literal(_,P,_,(V0,V4,V2,V1)),
    V3!=V2,
    singleton(V3).

:-
    body_literal(_,P,_,(V0,V2,V3,V1)),
    body_literal(_,P,_,(V0,V5,V4,V1)),
    V2!=V5,
    V3!=V4,
    singleton(V5),
    singleton(V4).

:-
    body_literal(_,P,_,(V0,V3,V5,V2)),
    body_literal(_,P,_,(V0,V3,V4,V1)),
    V5!=V3,
    V2!=V1,
    singleton(V4),
    singleton(V1).

:-
    body_literal(_,P,_,(V0,V4,V3,V2)),
    body_literal(_,P,_,(V0,V5,V6,V1)),
    V4!=V5,
    V3!=V6,
    V2!=V1,
    singleton(V5),
    singleton(V6),
    singleton(V1).
% schema info
schema(dblp_acm).

% er_type: 4 - default, 2 - object, 3 - value, 0 - tid
% attributes here should be independent to relations
attr(tid,0).
attr(did,2).
attr(dtitle,4).
attr(dauthors,4).
attr(dvenue,4).
attr(dyear,4).

% attr(a_tid,0).
attr(aid,2).
attr(atitle,4).
attr(aauthors,4).
attr(avenue,4).
attr(ayear,4).


compatible_attr(did,aid).
compatible_attr(dtitle,atitle).
compatible_attr(dauthors,aauthors).
compatible_attr(dvenue,avenue).
compatible_attr(dyear,ayear).
compatible_attr(X,Y) :- compatible_attr(Y,X).
compatible_attr(X,Y) :- compatible_attr(X,Z), compatible_attr(Z,Y).
compatible_attr(X,X) :- compatible_attr(X,_).

r(dblp_acm,dblp,6).
r(dblp_acm,acm,6).

has_sort(dblp,tid).
has_sort(dblp,did).
has_sort(dblp,dtitle).
has_sort(dblp,dauthors).
has_sort(dblp,dvenue).
has_sort(dblp,dyear).  


has_sort(acm,tid).
has_sort(acm,aid).
has_sort(acm,atitle).
has_sort(acm,aauthors).
has_sort(acm,avenue).
has_sort(acm,ayear).



% language constructs
head_pred(eqo,2).

% body_pred(dblp,1).
% body_pred(acm,1).
body_pred(sim,2).
body_pred(att,3).

const(att,2).

body_pred(R,1) :- r(_,R,_).

% type(eqo,(did,aid)).
% type(eqo,(aid,did)).
% type(sim,(dtitle,atitle)).

{type(eqo,(Aname1,Aname2));type(sim,(Aname1,Aname2))}=2 :- compatible_attr(Aname1,Aname2).
% :- compatible_attr(Aname1,Aname2).

% type(att,(d_tid,attr,did)).
% type(att,(a_tid,attr,aid)).
% type(att,(d_tid,attr,dtitle)).
% type(att,(a_tid,attr,atitle)).

% shall tid be a unified attribute?
type(att,(tid,attr,Aname)):- attr(Aname,_), Aname!= tid.
type(R,(tid)) :- r(_,R,_).


% type(dblp,(d_tid)).
% type(acm,(a_tid)).

target(dblp,did).
target(acm,aid).





max_clauses(1).
max_body(3).
max_vars(3).
head_vars(2, (0,1)).
vars(1, (0)).
var_pos(0, (0), 0).
ordered_vars((0), (0)).
vars(1, (1)).
var_pos(1, (1), 0).
ordered_vars((1), (1)).
vars(1, (2)).
var_pos(2, (2), 0).
ordered_vars((2), (2)).
vars(2, (0, 1)).
var_pos(0, (0, 1), 0).
var_pos(1, (0, 1), 1).
ordered_vars((0, 1), (0, 1)).
vars(2, (0, 2)).
var_pos(0, (0, 2), 0).
var_pos(2, (0, 2), 1).
ordered_vars((0, 2), (0, 2)).
vars(2, (1, 0)).
var_pos(1, (1, 0), 0).
var_pos(0, (1, 0), 1).
ordered_vars((1, 0), (0, 1)).
vars(2, (1, 2)).
var_pos(1, (1, 2), 0).
var_pos(2, (1, 2), 1).
ordered_vars((1, 2), (1, 2)).
vars(2, (2, 0)).
var_pos(2, (2, 0), 0).
var_pos(0, (2, 0), 1).
ordered_vars((2, 0), (0, 2)).
vars(2, (2, 1)).
var_pos(2, (2, 1), 0).
var_pos(1, (2, 1), 1).
ordered_vars((2, 1), (1, 2)).
vars(3, (0, 1, 2)).
var_pos(0, (0, 1, 2), 0).
var_pos(1, (0, 1, 2), 1).
var_pos(2, (0, 1, 2), 2).
ordered_vars((0, 1, 2), (0, 1, 2)).
vars(3, (0, 2, 1)).
var_pos(0, (0, 2, 1), 0).
var_pos(2, (0, 2, 1), 1).
var_pos(1, (0, 2, 1), 2).
ordered_vars((0, 2, 1), (0, 1, 2)).
vars(3, (1, 0, 2)).
var_pos(1, (1, 0, 2), 0).
var_pos(0, (1, 0, 2), 1).
var_pos(2, (1, 0, 2), 2).
ordered_vars((1, 0, 2), (0, 1, 2)).
vars(3, (1, 2, 0)).
var_pos(1, (1, 2, 0), 0).
var_pos(2, (1, 2, 0), 1).
var_pos(0, (1, 2, 0), 2).
ordered_vars((1, 2, 0), (0, 1, 2)).
vars(3, (2, 0, 1)).
var_pos(2, (2, 0, 1), 0).
var_pos(0, (2, 0, 1), 1).
var_pos(1, (2, 0, 1), 2).
ordered_vars((2, 0, 1), (0, 1, 2)).
vars(3, (2, 1, 0)).
var_pos(2, (2, 1, 0), 0).
var_pos(1, (2, 1, 0), 1).
var_pos(0, (2, 1, 0), 2).
ordered_vars((2, 1, 0), (0, 1, 2)).
vars(3, (0, tid, 2)).
var_pos(0, (0, tid, 2), 0).
const_pos(tid, (0, tid, 2), 1).
var_pos(2, (0, tid, 2), 2).
ordered_vars((0, tid, 2),(0, tid, 2)).
vars(3, (0, did, 2)).
var_pos(0, (0, did, 2), 0).
const_pos(did, (0, did, 2), 1).
var_pos(2, (0, did, 2), 2).
ordered_vars((0, did, 2),(0, did, 2)).
vars(3, (0, dtitle, 2)).
var_pos(0, (0, dtitle, 2), 0).
const_pos(dtitle, (0, dtitle, 2), 1).
var_pos(2, (0, dtitle, 2), 2).
ordered_vars((0, dtitle, 2),(0, dtitle, 2)).
vars(3, (0, dauthors, 2)).
var_pos(0, (0, dauthors, 2), 0).
const_pos(dauthors, (0, dauthors, 2), 1).
var_pos(2, (0, dauthors, 2), 2).
ordered_vars((0, dauthors, 2),(0, dauthors, 2)).
vars(3, (0, dvenue, 2)).
var_pos(0, (0, dvenue, 2), 0).
const_pos(dvenue, (0, dvenue, 2), 1).
var_pos(2, (0, dvenue, 2), 2).
ordered_vars((0, dvenue, 2),(0, dvenue, 2)).
vars(3, (0, dyear, 2)).
var_pos(0, (0, dyear, 2), 0).
const_pos(dyear, (0, dyear, 2), 1).
var_pos(2, (0, dyear, 2), 2).
ordered_vars((0, dyear, 2),(0, dyear, 2)).
vars(3, (0, aid, 2)).
var_pos(0, (0, aid, 2), 0).
const_pos(aid, (0, aid, 2), 1).
var_pos(2, (0, aid, 2), 2).
ordered_vars((0, aid, 2),(0, aid, 2)).
vars(3, (0, atitle, 2)).
var_pos(0, (0, atitle, 2), 0).
const_pos(atitle, (0, atitle, 2), 1).
var_pos(2, (0, atitle, 2), 2).
ordered_vars((0, atitle, 2),(0, atitle, 2)).
vars(3, (0, aauthors, 2)).
var_pos(0, (0, aauthors, 2), 0).
const_pos(aauthors, (0, aauthors, 2), 1).
var_pos(2, (0, aauthors, 2), 2).
ordered_vars((0, aauthors, 2),(0, aauthors, 2)).
vars(3, (0, avenue, 2)).
var_pos(0, (0, avenue, 2), 0).
const_pos(avenue, (0, avenue, 2), 1).
var_pos(2, (0, avenue, 2), 2).
ordered_vars((0, avenue, 2),(0, avenue, 2)).
vars(3, (0, ayear, 2)).
var_pos(0, (0, ayear, 2), 0).
const_pos(ayear, (0, ayear, 2), 1).
var_pos(2, (0, ayear, 2), 2).
ordered_vars((0, ayear, 2),(0, ayear, 2)).
vars(3, (0, tid, 1)).
var_pos(0, (0, tid, 1), 0).
const_pos(tid, (0, tid, 1), 1).
var_pos(1, (0, tid, 1), 2).
ordered_vars((0, tid, 1),(0, tid, 1)).
vars(3, (0, did, 1)).
var_pos(0, (0, did, 1), 0).
const_pos(did, (0, did, 1), 1).
var_pos(1, (0, did, 1), 2).
ordered_vars((0, did, 1),(0, did, 1)).
vars(3, (0, dtitle, 1)).
var_pos(0, (0, dtitle, 1), 0).
const_pos(dtitle, (0, dtitle, 1), 1).
var_pos(1, (0, dtitle, 1), 2).
ordered_vars((0, dtitle, 1),(0, dtitle, 1)).
vars(3, (0, dauthors, 1)).
var_pos(0, (0, dauthors, 1), 0).
const_pos(dauthors, (0, dauthors, 1), 1).
var_pos(1, (0, dauthors, 1), 2).
ordered_vars((0, dauthors, 1),(0, dauthors, 1)).
vars(3, (0, dvenue, 1)).
var_pos(0, (0, dvenue, 1), 0).
const_pos(dvenue, (0, dvenue, 1), 1).
var_pos(1, (0, dvenue, 1), 2).
ordered_vars((0, dvenue, 1),(0, dvenue, 1)).
vars(3, (0, dyear, 1)).
var_pos(0, (0, dyear, 1), 0).
const_pos(dyear, (0, dyear, 1), 1).
var_pos(1, (0, dyear, 1), 2).
ordered_vars((0, dyear, 1),(0, dyear, 1)).
vars(3, (0, aid, 1)).
var_pos(0, (0, aid, 1), 0).
const_pos(aid, (0, aid, 1), 1).
var_pos(1, (0, aid, 1), 2).
ordered_vars((0, aid, 1),(0, aid, 1)).
vars(3, (0, atitle, 1)).
var_pos(0, (0, atitle, 1), 0).
const_pos(atitle, (0, atitle, 1), 1).
var_pos(1, (0, atitle, 1), 2).
ordered_vars((0, atitle, 1),(0, atitle, 1)).
vars(3, (0, aauthors, 1)).
var_pos(0, (0, aauthors, 1), 0).
const_pos(aauthors, (0, aauthors, 1), 1).
var_pos(1, (0, aauthors, 1), 2).
ordered_vars((0, aauthors, 1),(0, aauthors, 1)).
vars(3, (0, avenue, 1)).
var_pos(0, (0, avenue, 1), 0).
const_pos(avenue, (0, avenue, 1), 1).
var_pos(1, (0, avenue, 1), 2).
ordered_vars((0, avenue, 1),(0, avenue, 1)).
vars(3, (0, ayear, 1)).
var_pos(0, (0, ayear, 1), 0).
const_pos(ayear, (0, ayear, 1), 1).
var_pos(1, (0, ayear, 1), 2).
ordered_vars((0, ayear, 1),(0, ayear, 1)).
vars(3, (1, tid, 2)).
var_pos(1, (1, tid, 2), 0).
const_pos(tid, (1, tid, 2), 1).
var_pos(2, (1, tid, 2), 2).
ordered_vars((1, tid, 2),(1, tid, 2)).
vars(3, (1, did, 2)).
var_pos(1, (1, did, 2), 0).
const_pos(did, (1, did, 2), 1).
var_pos(2, (1, did, 2), 2).
ordered_vars((1, did, 2),(1, did, 2)).
vars(3, (1, dtitle, 2)).
var_pos(1, (1, dtitle, 2), 0).
const_pos(dtitle, (1, dtitle, 2), 1).
var_pos(2, (1, dtitle, 2), 2).
ordered_vars((1, dtitle, 2),(1, dtitle, 2)).
vars(3, (1, dauthors, 2)).
var_pos(1, (1, dauthors, 2), 0).
const_pos(dauthors, (1, dauthors, 2), 1).
var_pos(2, (1, dauthors, 2), 2).
ordered_vars((1, dauthors, 2),(1, dauthors, 2)).
vars(3, (1, dvenue, 2)).
var_pos(1, (1, dvenue, 2), 0).
const_pos(dvenue, (1, dvenue, 2), 1).
var_pos(2, (1, dvenue, 2), 2).
ordered_vars((1, dvenue, 2),(1, dvenue, 2)).
vars(3, (1, dyear, 2)).
var_pos(1, (1, dyear, 2), 0).
const_pos(dyear, (1, dyear, 2), 1).
var_pos(2, (1, dyear, 2), 2).
ordered_vars((1, dyear, 2),(1, dyear, 2)).
vars(3, (1, aid, 2)).
var_pos(1, (1, aid, 2), 0).
const_pos(aid, (1, aid, 2), 1).
var_pos(2, (1, aid, 2), 2).
ordered_vars((1, aid, 2),(1, aid, 2)).
vars(3, (1, atitle, 2)).
var_pos(1, (1, atitle, 2), 0).
const_pos(atitle, (1, atitle, 2), 1).
var_pos(2, (1, atitle, 2), 2).
ordered_vars((1, atitle, 2),(1, atitle, 2)).
vars(3, (1, aauthors, 2)).
var_pos(1, (1, aauthors, 2), 0).
const_pos(aauthors, (1, aauthors, 2), 1).
var_pos(2, (1, aauthors, 2), 2).
ordered_vars((1, aauthors, 2),(1, aauthors, 2)).
vars(3, (1, avenue, 2)).
var_pos(1, (1, avenue, 2), 0).
const_pos(avenue, (1, avenue, 2), 1).
var_pos(2, (1, avenue, 2), 2).
ordered_vars((1, avenue, 2),(1, avenue, 2)).
vars(3, (1, ayear, 2)).
var_pos(1, (1, ayear, 2), 0).
const_pos(ayear, (1, ayear, 2), 1).
var_pos(2, (1, ayear, 2), 2).
ordered_vars((1, ayear, 2),(1, ayear, 2)).
vars(3, (1, tid, 0)).
var_pos(1, (1, tid, 0), 0).
const_pos(tid, (1, tid, 0), 1).
var_pos(0, (1, tid, 0), 2).
ordered_vars((1, tid, 0),(0, tid, 1)).
vars(3, (1, did, 0)).
var_pos(1, (1, did, 0), 0).
const_pos(did, (1, did, 0), 1).
var_pos(0, (1, did, 0), 2).
ordered_vars((1, did, 0),(0, did, 1)).
vars(3, (1, dtitle, 0)).
var_pos(1, (1, dtitle, 0), 0).
const_pos(dtitle, (1, dtitle, 0), 1).
var_pos(0, (1, dtitle, 0), 2).
ordered_vars((1, dtitle, 0),(0, dtitle, 1)).
vars(3, (1, dauthors, 0)).
var_pos(1, (1, dauthors, 0), 0).
const_pos(dauthors, (1, dauthors, 0), 1).
var_pos(0, (1, dauthors, 0), 2).
ordered_vars((1, dauthors, 0),(0, dauthors, 1)).
vars(3, (1, dvenue, 0)).
var_pos(1, (1, dvenue, 0), 0).
const_pos(dvenue, (1, dvenue, 0), 1).
var_pos(0, (1, dvenue, 0), 2).
ordered_vars((1, dvenue, 0),(0, dvenue, 1)).
vars(3, (1, dyear, 0)).
var_pos(1, (1, dyear, 0), 0).
const_pos(dyear, (1, dyear, 0), 1).
var_pos(0, (1, dyear, 0), 2).
ordered_vars((1, dyear, 0),(0, dyear, 1)).
vars(3, (1, aid, 0)).
var_pos(1, (1, aid, 0), 0).
const_pos(aid, (1, aid, 0), 1).
var_pos(0, (1, aid, 0), 2).
ordered_vars((1, aid, 0),(0, aid, 1)).
vars(3, (1, atitle, 0)).
var_pos(1, (1, atitle, 0), 0).
const_pos(atitle, (1, atitle, 0), 1).
var_pos(0, (1, atitle, 0), 2).
ordered_vars((1, atitle, 0),(0, atitle, 1)).
vars(3, (1, aauthors, 0)).
var_pos(1, (1, aauthors, 0), 0).
const_pos(aauthors, (1, aauthors, 0), 1).
var_pos(0, (1, aauthors, 0), 2).
ordered_vars((1, aauthors, 0),(0, aauthors, 1)).
vars(3, (1, avenue, 0)).
var_pos(1, (1, avenue, 0), 0).
const_pos(avenue, (1, avenue, 0), 1).
var_pos(0, (1, avenue, 0), 2).
ordered_vars((1, avenue, 0),(0, avenue, 1)).
vars(3, (1, ayear, 0)).
var_pos(1, (1, ayear, 0), 0).
const_pos(ayear, (1, ayear, 0), 1).
var_pos(0, (1, ayear, 0), 2).
ordered_vars((1, ayear, 0),(0, ayear, 1)).
vars(3, (2, tid, 1)).
var_pos(2, (2, tid, 1), 0).
const_pos(tid, (2, tid, 1), 1).
var_pos(1, (2, tid, 1), 2).
ordered_vars((2, tid, 1),(1, tid, 2)).
vars(3, (2, did, 1)).
var_pos(2, (2, did, 1), 0).
const_pos(did, (2, did, 1), 1).
var_pos(1, (2, did, 1), 2).
ordered_vars((2, did, 1),(1, did, 2)).
vars(3, (2, dtitle, 1)).
var_pos(2, (2, dtitle, 1), 0).
const_pos(dtitle, (2, dtitle, 1), 1).
var_pos(1, (2, dtitle, 1), 2).
ordered_vars((2, dtitle, 1),(1, dtitle, 2)).
vars(3, (2, dauthors, 1)).
var_pos(2, (2, dauthors, 1), 0).
const_pos(dauthors, (2, dauthors, 1), 1).
var_pos(1, (2, dauthors, 1), 2).
ordered_vars((2, dauthors, 1),(1, dauthors, 2)).
vars(3, (2, dvenue, 1)).
var_pos(2, (2, dvenue, 1), 0).
const_pos(dvenue, (2, dvenue, 1), 1).
var_pos(1, (2, dvenue, 1), 2).
ordered_vars((2, dvenue, 1),(1, dvenue, 2)).
vars(3, (2, dyear, 1)).
var_pos(2, (2, dyear, 1), 0).
const_pos(dyear, (2, dyear, 1), 1).
var_pos(1, (2, dyear, 1), 2).
ordered_vars((2, dyear, 1),(1, dyear, 2)).
vars(3, (2, aid, 1)).
var_pos(2, (2, aid, 1), 0).
const_pos(aid, (2, aid, 1), 1).
var_pos(1, (2, aid, 1), 2).
ordered_vars((2, aid, 1),(1, aid, 2)).
vars(3, (2, atitle, 1)).
var_pos(2, (2, atitle, 1), 0).
const_pos(atitle, (2, atitle, 1), 1).
var_pos(1, (2, atitle, 1), 2).
ordered_vars((2, atitle, 1),(1, atitle, 2)).
vars(3, (2, aauthors, 1)).
var_pos(2, (2, aauthors, 1), 0).
const_pos(aauthors, (2, aauthors, 1), 1).
var_pos(1, (2, aauthors, 1), 2).
ordered_vars((2, aauthors, 1),(1, aauthors, 2)).
vars(3, (2, avenue, 1)).
var_pos(2, (2, avenue, 1), 0).
const_pos(avenue, (2, avenue, 1), 1).
var_pos(1, (2, avenue, 1), 2).
ordered_vars((2, avenue, 1),(1, avenue, 2)).
vars(3, (2, ayear, 1)).
var_pos(2, (2, ayear, 1), 0).
const_pos(ayear, (2, ayear, 1), 1).
var_pos(1, (2, ayear, 1), 2).
ordered_vars((2, ayear, 1),(1, ayear, 2)).
vars(3, (2, tid, 0)).
var_pos(2, (2, tid, 0), 0).
const_pos(tid, (2, tid, 0), 1).
var_pos(0, (2, tid, 0), 2).
ordered_vars((2, tid, 0),(0, tid, 2)).
vars(3, (2, did, 0)).
var_pos(2, (2, did, 0), 0).
const_pos(did, (2, did, 0), 1).
var_pos(0, (2, did, 0), 2).
ordered_vars((2, did, 0),(0, did, 2)).
vars(3, (2, dtitle, 0)).
var_pos(2, (2, dtitle, 0), 0).
const_pos(dtitle, (2, dtitle, 0), 1).
var_pos(0, (2, dtitle, 0), 2).
ordered_vars((2, dtitle, 0),(0, dtitle, 2)).
vars(3, (2, dauthors, 0)).
var_pos(2, (2, dauthors, 0), 0).
const_pos(dauthors, (2, dauthors, 0), 1).
var_pos(0, (2, dauthors, 0), 2).
ordered_vars((2, dauthors, 0),(0, dauthors, 2)).
vars(3, (2, dvenue, 0)).
var_pos(2, (2, dvenue, 0), 0).
const_pos(dvenue, (2, dvenue, 0), 1).
var_pos(0, (2, dvenue, 0), 2).
ordered_vars((2, dvenue, 0),(0, dvenue, 2)).
vars(3, (2, dyear, 0)).
var_pos(2, (2, dyear, 0), 0).
const_pos(dyear, (2, dyear, 0), 1).
var_pos(0, (2, dyear, 0), 2).
ordered_vars((2, dyear, 0),(0, dyear, 2)).
vars(3, (2, aid, 0)).
var_pos(2, (2, aid, 0), 0).
const_pos(aid, (2, aid, 0), 1).
var_pos(0, (2, aid, 0), 2).
ordered_vars((2, aid, 0),(0, aid, 2)).
vars(3, (2, atitle, 0)).
var_pos(2, (2, atitle, 0), 0).
const_pos(atitle, (2, atitle, 0), 1).
var_pos(0, (2, atitle, 0), 2).
ordered_vars((2, atitle, 0),(0, atitle, 2)).
vars(3, (2, aauthors, 0)).
var_pos(2, (2, aauthors, 0), 0).
const_pos(aauthors, (2, aauthors, 0), 1).
var_pos(0, (2, aauthors, 0), 2).
ordered_vars((2, aauthors, 0),(0, aauthors, 2)).
vars(3, (2, avenue, 0)).
var_pos(2, (2, avenue, 0), 0).
const_pos(avenue, (2, avenue, 0), 1).
var_pos(0, (2, avenue, 0), 2).
ordered_vars((2, avenue, 0),(0, avenue, 2)).
vars(3, (2, ayear, 0)).
var_pos(2, (2, ayear, 0), 0).
const_pos(ayear, (2, ayear, 0), 1).
var_pos(0, (2, ayear, 0), 2).
ordered_vars((2, ayear, 0),(0, ayear, 2)).
appears((0,V0,V1)):- body_literal(_,_,_,(X0,X1)), ordered_vars((X0,X1), (V0,V1)).
var_tuple((0,V0,V1)):- body_pred(P,2), vars(2,Vars), not bad_body(P,Vars), not type_mismatch(P,Vars), ordered_vars(Vars,OrderedVars), OrderedVars=(V0,V1).
var_member(V,(0,V0,V1)):-vars(_, Vars), Vars=(V0,V1), var_member(V,Vars).
appears((V0,V1,V2)):- body_literal(_,_,_,(X0,X1,X2)), ordered_vars((X0,X1,X2), (V0,V1,V2)).
var_tuple((V0,V1,V2)):- body_pred(P,3), vars(3,Vars), not bad_body(P,Vars), not type_mismatch(P,Vars), ordered_vars(Vars,OrderedVars), OrderedVars=(V0,V1,V2).
var_member(V,(V0,V1,V2)):-vars(_, Vars), Vars=(V0,V1,V2), var_member(V,Vars).
lower((V0,V1,V2),(X0,X1,X2)):- var_tuple((V0,V1,V2)), var_tuple((X0,X1,X2)), X0 < V0.
lower((V0,V1,V2),(V0,X1,X2)):- var_tuple((V0,V1,V2)), var_tuple((V0,X1,X2)), X1 < V1.
lower((V0,V1,V2),(V0,V1,X2)):- var_tuple((V0,V1,V2)), var_tuple((V0,V1,X2)), X2 < V2.
seen_lower(Vars1, V):- V=V1-1, Vars1 = (V0,V1,V2), V0 < V < V1, lower(Vars1, Vars2), var_tuple(Vars1), appears(Vars2), var_member(V, Vars2), not head_var(_,V).
gap_((V0,V1,V2),V1-1):- var_tuple((V0,V1,V2)), V0 < V < V1, var(V).
seen_lower(Vars1, V):- V=V2-1, Vars1 = (V0,V1,V2), V1 < V < V2, lower(Vars1, Vars2), var_tuple(Vars1), appears(Vars2), var_member(V, Vars2), not head_var(_,V).
gap_((V0,V1,V2),V2-1):- var_tuple((V0,V1,V2)), V1 < V < V2, var(V).
gap((V0,V1,V2),V):- gap_((V0,V1,V2), _), #max{X :gap_((V0,V1,V2), X)} == V.
:- appears((V0,V1,V2)), gap((V0,V1,V2), V), not seen_lower((V0,V1,V2),V), not head_var(_,V).
type_pos((aauthors,dauthors), 1, dauthors).
type_pos((dvenue,dvenue), 1, dvenue).
type_pos((avenue,dvenue), 0, avenue).
type_pos((tid,attr,dtitle), 0, tid).
type_pos((tid,attr,dyear), 1, attr).
type_pos((dvenue,avenue), 0, dvenue).
type_pos((tid,attr,aauthors), 1, attr).
type_pos((tid,attr,avenue), 1, attr).
type_pos((tid,attr,dvenue), 0, tid).
type_pos((ayear,dyear), 0, ayear).
type_pos((dyear,ayear), 0, dyear).
type_pos((dyear,dyear), 0, dyear).
type_pos((tid,attr,dauthors), 0, tid).
type_pos((dyear,dyear), 1, dyear).
type_pos((dtitle,dtitle), 0, dtitle).
type_pos((did,did), 1, did).
type_pos((avenue,dvenue), 1, dvenue).
type_pos((atitle,atitle), 0, atitle).
type_pos((ayear,ayear), 1, ayear).
type_pos((tid,attr,did), 2, did).
type_pos((tid,attr,did), 1, attr).
type_pos((tid,attr,atitle), 2, atitle).
type_pos((dtitle,atitle), 0, dtitle).
type_pos((dtitle,dtitle), 1, dtitle).
type_pos((atitle,atitle), 1, atitle).
type_pos((tid,attr,dvenue), 1, attr).
type_pos((tid,attr,atitle), 0, tid).
type_pos((tid,attr,dtitle), 2, dtitle).
type_pos((tid,attr,dtitle), 1, attr).
type_pos((tid,attr,dauthors), 2, dauthors).
type_pos((tid,attr,dvenue), 2, dvenue).
type_pos((tid,attr,dauthors), 1, attr).
type_pos((tid,attr,ayear), 0, tid).
type_pos((dyear,ayear), 1, ayear).
type_pos((tid,attr,dyear), 0, tid).
type_pos((dvenue,avenue), 1, avenue).
type_pos((dvenue,dvenue), 0, dvenue).
type_pos((tid,attr,aauthors), 2, aauthors).
type_pos((tid,attr,ayear), 2, ayear).
type_pos((ayear,ayear), 0, ayear).
type_pos((did,did), 0, did).
type_pos((avenue,avenue), 1, avenue).
type_pos((aauthors,dauthors), 0, aauthors).
type_pos((atitle,dtitle), 0, atitle).
type_pos((aauthors,aauthors), 0, aauthors).
type_pos((dauthors,aauthors), 0, dauthors).
type_pos((did,aid), 1, aid).
type_pos((tid,attr,dyear), 2, dyear).
type_pos((atitle,dtitle), 1, dtitle).
type_pos((tid,attr,atitle), 1, attr).
type_pos((aid,did), 0, aid).
type_pos((dtitle,atitle), 1, atitle).
type_pos((tid,attr,avenue), 2, avenue).
type_pos((avenue,avenue), 0, avenue).
type_pos((aid,did), 1, did).
type_pos((aid,aid), 0, aid).
type_pos((tid,attr,aid), 2, aid).
type_pos((tid,attr,aid), 1, attr).
type_pos((tid,attr,ayear), 1, attr).
type_pos((tid,attr,avenue), 0, tid).
type_pos((did,aid), 0, did).
type_pos((ayear,dyear), 1, dyear).
type_pos((aauthors,aauthors), 1, aauthors).
type_pos((tid,attr,aid), 0, tid).
type_pos((tid,attr,aauthors), 0, tid).
type_pos((tid), 0, tid).
type_pos((tid,attr,did), 0, tid).
type_pos((dauthors,dauthors), 0, dauthors).
type_pos((dauthors,aauthors), 1, aauthors).
type_pos((dauthors,dauthors), 1, dauthors).
type_pos((aid,aid), 1, aid).
:- body_literal(Rule,sim,_,(_,_)), #count{V0,V1: body_literal(Rule,sim,_,(V0,V1))} > 2.
:- body_literal(Rule,sim,_,(_,V1)), #count{V0: body_literal(Rule,sim,_,(V0,V1))} > 1.
:- body_literal(Rule,sim,_,(V0,_)), #count{V1: body_literal(Rule,sim,_,(V0,V1))} > 1.
:- body_literal(Rule,att,_,(_,_,V2)), #count{V0,V1: body_literal(Rule,att,_,(V0,V1,V2))} > 1.
:- body_literal(Rule,att,_,(_,V1,_)), #count{V0,V2: body_literal(Rule,att,_,(V0,V1,V2))} > 2.
:- body_literal(Rule,att,_,(_,V1,V2)), #count{V0: body_literal(Rule,att,_,(V0,V1,V2))} > 1.
:- body_literal(Rule,att,_,(V0,_,_)), #count{V1,V2: body_literal(Rule,att,_,(V0,V1,V2))} > 2.
:- body_literal(Rule,att,_,(V0,_,V2)), #count{V1: body_literal(Rule,att,_,(V0,V1,V2))} > 1.
:- body_literal(Rule,att,_,(V0,V1,_)), #count{V2: body_literal(Rule,att,_,(V0,V1,V2))} > 1.
:- body_literal(Rule,dblp,_,(_,)), #count{V0: body_literal(Rule,dblp,_,(V0,))} > 2.
:- body_literal(Rule,acm,_,(_,)), #count{V0: body_literal(Rule,acm,_,(V0,))} > 2.
:- body_literal(_, att, _, (V0,V1,V2)), singleton(V1),singleton(V2).
:- body_literal(_, att, _, (V0,V1,V2)), singleton(V0),singleton(V2).
:- body_literal(_, att, _, (V0,V1,V2)), singleton(V0),singleton(V1).
prop(ab_ba,(sim,sim)).
prop(ab_ac_ca,(sim,sim,sim)).
prop(not_ab_bc_ac,(sim,sim,sim)).
prop(not_ab_ac_cb,(sim,sim,sim)).
prop(not_ab_ca_bc,(sim,sim,sim)).
prop(not_a_a,(acm,dblp)).
prop(not_ab_ca_cb,(sim,sim,sim)).
prop(ab_bc_cb,(sim,sim,sim)).
:- prop(not_abc_bca,(P,Q)), body_literal(Rule,P,_,(A,B,C)), body_literal(Rule,Q,_,(B,C,A)).
:- prop(abc_bca,(P,Q)), body_literal(Rule,P,_,(A,B,C)), body_literal(Rule,Q,_,(B,C,A)), valid_var(Rule,B),valid_var(Rule,C),valid_var(Rule,A).
:- prop(not_abc_bac,(P,Q)), body_literal(Rule,P,_,(A,B,C)), body_literal(Rule,Q,_,(B,A,C)).
:- prop(abc_bac,(P,Q)), body_literal(Rule,P,_,(A,B,C)), body_literal(Rule,Q,_,(B,A,C)), valid_var(Rule,B),valid_var(Rule,C),valid_var(Rule,A).
:- prop(not_abc_c,(P,Q)), body_literal(Rule,P,_,(A,B,C)), body_literal(Rule,Q,_,(C,)).
:- prop(abc_c,(P,Q)), body_literal(Rule,P,_,(A,B,C)), body_literal(Rule,Q,_,(C,)), valid_var(Rule,C).
:- prop(not_abc_ba,(P,Q)), body_literal(Rule,P,_,(A,B,C)), body_literal(Rule,Q,_,(B,A)).
:- prop(abc_ba,(P,Q)), body_literal(Rule,P,_,(A,B,C)), body_literal(Rule,Q,_,(B,A)), valid_var(Rule,B),valid_var(Rule,A).
:- prop(not_abc_ca,(P,Q)), body_literal(Rule,P,_,(A,B,C)), body_literal(Rule,Q,_,(C,A)).
:- prop(abc_ca,(P,Q)), body_literal(Rule,P,_,(A,B,C)), body_literal(Rule,Q,_,(C,A)), valid_var(Rule,C),valid_var(Rule,A).
:- prop(not_abc_ac,(P,Q)), body_literal(Rule,P,_,(A,B,C)), body_literal(Rule,Q,_,(A,C)).
:- prop(abc_ac,(P,Q)), body_literal(Rule,P,_,(A,B,C)), body_literal(Rule,Q,_,(A,C)), valid_var(Rule,C),valid_var(Rule,A).
:- prop(not_abc_cb,(P,Q)), body_literal(Rule,P,_,(A,B,C)), body_literal(Rule,Q,_,(C,B)).
:- prop(abc_cb,(P,Q)), body_literal(Rule,P,_,(A,B,C)), body_literal(Rule,Q,_,(C,B)), valid_var(Rule,B),valid_var(Rule,C).
:- prop(not_abc_cba,(P,Q)), body_literal(Rule,P,_,(A,B,C)), body_literal(Rule,Q,_,(C,B,A)).
:- prop(abc_cba,(P,Q)), body_literal(Rule,P,_,(A,B,C)), body_literal(Rule,Q,_,(C,B,A)), valid_var(Rule,B),valid_var(Rule,C),valid_var(Rule,A).
:- prop(not_ab_ba,(P,Q)), body_literal(Rule,P,_,(A,B)), body_literal(Rule,Q,_,(B,A)).
:- prop(ab_ba,(P,Q)), body_literal(Rule,P,_,(A,B)), body_literal(Rule,Q,_,(B,A)), valid_var(Rule,B),valid_var(Rule,A).
:- prop(not_ab_ca,(P,Q)), body_literal(Rule,P,_,(A,B)), body_literal(Rule,Q,_,(_,A)).
:- prop(not_ab_ac,(P,Q)), body_literal(Rule,P,_,(A,B)), body_literal(Rule,Q,_,(A,_)).
:- prop(not_ab_cb,(P,Q)), body_literal(Rule,P,_,(A,B)), body_literal(Rule,Q,_,(_,B)).
:- prop(not_abc_a,(P,Q)), body_literal(Rule,P,_,(A,B,C)), body_literal(Rule,Q,_,(A,)).
:- prop(abc_a,(P,Q)), body_literal(Rule,P,_,(A,B,C)), body_literal(Rule,Q,_,(A,)), valid_var(Rule,A).
:- prop(not_abc_cab,(P,Q)), body_literal(Rule,P,_,(A,B,C)), body_literal(Rule,Q,_,(C,A,B)).
:- prop(abc_cab,(P,Q)), body_literal(Rule,P,_,(A,B,C)), body_literal(Rule,Q,_,(C,A,B)), valid_var(Rule,B),valid_var(Rule,C),valid_var(Rule,A).
:- prop(not_abc_b,(P,Q)), body_literal(Rule,P,_,(A,B,C)), body_literal(Rule,Q,_,(B,)).
:- prop(abc_b,(P,Q)), body_literal(Rule,P,_,(A,B,C)), body_literal(Rule,Q,_,(B,)), valid_var(Rule,B).
:- prop(not_abc_abc,(P,Q)), body_literal(Rule,P,_,(A,B,C)), body_literal(Rule,Q,_,(A,B,C)).
:- prop(abc_abc,(P,Q)), body_literal(Rule,P,_,(A,B,C)), body_literal(Rule,Q,_,(A,B,C)), valid_var(Rule,B),valid_var(Rule,C),valid_var(Rule,A).
:- prop(not_abc_ab,(P,Q)), body_literal(Rule,P,_,(A,B,C)), body_literal(Rule,Q,_,(A,B)).
:- prop(abc_ab,(P,Q)), body_literal(Rule,P,_,(A,B,C)), body_literal(Rule,Q,_,(A,B)), valid_var(Rule,B),valid_var(Rule,A).
:- prop(not_ab_a,(P,Q)), body_literal(Rule,P,_,(A,B)), body_literal(Rule,Q,_,(A,)).
:- prop(ab_a,(P,Q)), body_literal(Rule,P,_,(A,B)), body_literal(Rule,Q,_,(A,)), valid_var(Rule,A).
:- prop(not_ab_b,(P,Q)), body_literal(Rule,P,_,(A,B)), body_literal(Rule,Q,_,(B,)).
:- prop(ab_b,(P,Q)), body_literal(Rule,P,_,(A,B)), body_literal(Rule,Q,_,(B,)), valid_var(Rule,B).
:- prop(not_abc_bc,(P,Q)), body_literal(Rule,P,_,(A,B,C)), body_literal(Rule,Q,_,(B,C)).
:- prop(abc_bc,(P,Q)), body_literal(Rule,P,_,(A,B,C)), body_literal(Rule,Q,_,(B,C)), valid_var(Rule,B),valid_var(Rule,C).
:- prop(not_ab_ab,(P,Q)), body_literal(Rule,P,_,(A,B)), body_literal(Rule,Q,_,(A,B)).
:- prop(ab_ab,(P,Q)), body_literal(Rule,P,_,(A,B)), body_literal(Rule,Q,_,(A,B)), valid_var(Rule,B),valid_var(Rule,A).
:- prop(not_a_a,(P,Q)), body_literal(Rule,P,_,(A,)), body_literal(Rule,Q,_,(A,)).
:- prop(a_a,(P,Q)), body_literal(Rule,P,_,(A,)), body_literal(Rule,Q,_,(A,)), valid_var(Rule,A).
:- prop(not_ab_bc,(P,Q)), body_literal(Rule,P,_,(A,B)), body_literal(Rule,Q,_,(B,_)).
:- prop(not_abc_acb,(P,Q)), body_literal(Rule,P,_,(A,B,C)), body_literal(Rule,Q,_,(A,C,B)).
:- prop(abc_acb,(P,Q)), body_literal(Rule,P,_,(A,B,C)), body_literal(Rule,Q,_,(A,C,B)), valid_var(Rule,B),valid_var(Rule,C),valid_var(Rule,A).
:- prop(not_ab_ca_bc,(P,Q,R)), body_literal(Rule,P,_,(A,B)), body_literal(Rule,Q,_,(C,A)), body_literal(Rule,R,_,(B,C)).
:- prop(ab_ca_bc,(P,Q,R)), body_literal(Rule,P,_,(A,B)), body_literal(Rule,Q,_,(C,A)), body_literal(Rule,R,_,(B,C)), valid_var(Rule,B),valid_var(Rule,C).
:- prop(not_ab_ab_ac,(P,Q,R)), body_literal(Rule,P,_,(A,B)), body_literal(Rule,Q,_,(A,B)), body_literal(Rule,R,_,(A,C)).
:- prop(not_ab_ac_c,(P,Q,R)), body_literal(Rule,P,_,(A,B)), body_literal(Rule,Q,_,(A,C)), body_literal(Rule,R,_,(C,)).
:- prop(ab_ac_c,(P,Q,R)), body_literal(Rule,P,_,(A,B)), body_literal(Rule,Q,_,(A,C)), body_literal(Rule,R,_,(C,)), valid_var(Rule,C).
:- prop(not_ab_b_b,(P,Q,R)), body_literal(Rule,P,_,(A,B)), body_literal(Rule,Q,_,(B,)), body_literal(Rule,R,_,(B,)).
:- prop(ab_b_b,(P,Q,R)), body_literal(Rule,P,_,(A,B)), body_literal(Rule,Q,_,(B,)), body_literal(Rule,R,_,(B,)), valid_var(Rule,B).
:- prop(not_ab_ac_ba,(P,Q,R)), body_literal(Rule,P,_,(A,B)), body_literal(Rule,Q,_,(A,C)), body_literal(Rule,R,_,(B,A)).
:- prop(ab_ac_ba,(P,Q,R)), body_literal(Rule,P,_,(A,B)), body_literal(Rule,Q,_,(A,C)), body_literal(Rule,R,_,(B,A)), valid_var(Rule,B),valid_var(Rule,A).
:- prop(not_ab_ac_ca,(P,Q,R)), body_literal(Rule,P,_,(A,B)), body_literal(Rule,Q,_,(A,C)), body_literal(Rule,R,_,(C,A)).
:- prop(ab_ac_ca,(P,Q,R)), body_literal(Rule,P,_,(A,B)), body_literal(Rule,Q,_,(A,C)), body_literal(Rule,R,_,(C,A)), valid_var(Rule,C),valid_var(Rule,A).
:- prop(not_ab_ab_cb,(P,Q,R)), body_literal(Rule,P,_,(A,B)), body_literal(Rule,Q,_,(A,B)), body_literal(Rule,R,_,(C,B)).
:- prop(not_ab_ba_ab,(P,Q,R)), body_literal(Rule,P,_,(A,B)), body_literal(Rule,Q,_,(B,A)), body_literal(Rule,R,_,(A,B)).
:- prop(ab_ba_ab,(P,Q,R)), body_literal(Rule,P,_,(A,B)), body_literal(Rule,Q,_,(B,A)), body_literal(Rule,R,_,(A,B)), valid_var(Rule,B),valid_var(Rule,A).
:- prop(not_ab_cb_a,(P,Q,R)), body_literal(Rule,P,_,(A,B)), body_literal(Rule,Q,_,(C,B)), body_literal(Rule,R,_,(A,)).
:- prop(ab_cb_a,(P,Q,R)), body_literal(Rule,P,_,(A,B)), body_literal(Rule,Q,_,(C,B)), body_literal(Rule,R,_,(A,)), valid_var(Rule,A).
:- prop(not_ab_ac_cb,(P,Q,R)), body_literal(Rule,P,_,(A,B)), body_literal(Rule,Q,_,(A,C)), body_literal(Rule,R,_,(C,B)).
:- prop(ab_ac_cb,(P,Q,R)), body_literal(Rule,P,_,(A,B)), body_literal(Rule,Q,_,(A,C)), body_literal(Rule,R,_,(C,B)), valid_var(Rule,B),valid_var(Rule,C).
:- prop(not_ab_bc_ba,(P,Q,R)), body_literal(Rule,P,_,(A,B)), body_literal(Rule,Q,_,(B,C)), body_literal(Rule,R,_,(B,A)).
:- prop(ab_bc_ba,(P,Q,R)), body_literal(Rule,P,_,(A,B)), body_literal(Rule,Q,_,(B,C)), body_literal(Rule,R,_,(B,A)), valid_var(Rule,B),valid_var(Rule,A).
:- prop(not_ab_bc_c,(P,Q,R)), body_literal(Rule,P,_,(A,B)), body_literal(Rule,Q,_,(B,C)), body_literal(Rule,R,_,(C,)).
:- prop(ab_bc_c,(P,Q,R)), body_literal(Rule,P,_,(A,B)), body_literal(Rule,Q,_,(B,C)), body_literal(Rule,R,_,(C,)), valid_var(Rule,C).
:- prop(not_ab_cb_b,(P,Q,R)), body_literal(Rule,P,_,(A,B)), body_literal(Rule,Q,_,(C,B)), body_literal(Rule,R,_,(B,)).
:- prop(ab_cb_b,(P,Q,R)), body_literal(Rule,P,_,(A,B)), body_literal(Rule,Q,_,(C,B)), body_literal(Rule,R,_,(B,)), valid_var(Rule,B).
:- prop(not_ab_bc_ac,(P,Q,R)), body_literal(Rule,P,_,(A,B)), body_literal(Rule,Q,_,(B,C)), body_literal(Rule,R,_,(A,C)).
:- prop(ab_bc_ac,(P,Q,R)), body_literal(Rule,P,_,(A,B)), body_literal(Rule,Q,_,(B,C)), body_literal(Rule,R,_,(A,C)), valid_var(Rule,C),valid_var(Rule,A).
:- prop(not_ab_ab_a,(P,Q,R)), body_literal(Rule,P,_,(A,B)), body_literal(Rule,Q,_,(A,B)), body_literal(Rule,R,_,(A,)).
:- prop(ab_ab_a,(P,Q,R)), body_literal(Rule,P,_,(A,B)), body_literal(Rule,Q,_,(A,B)), body_literal(Rule,R,_,(A,)), valid_var(Rule,A).
:- prop(not_ab_bc_cb,(P,Q,R)), body_literal(Rule,P,_,(A,B)), body_literal(Rule,Q,_,(B,C)), body_literal(Rule,R,_,(C,B)).
:- prop(ab_bc_cb,(P,Q,R)), body_literal(Rule,P,_,(A,B)), body_literal(Rule,Q,_,(B,C)), body_literal(Rule,R,_,(C,B)), valid_var(Rule,B),valid_var(Rule,C).
:- prop(not_ab_ca_c,(P,Q,R)), body_literal(Rule,P,_,(A,B)), body_literal(Rule,Q,_,(C,A)), body_literal(Rule,R,_,(C,)).
:- prop(ab_ca_c,(P,Q,R)), body_literal(Rule,P,_,(A,B)), body_literal(Rule,Q,_,(C,A)), body_literal(Rule,R,_,(C,)), valid_var(Rule,C).
:- prop(not_ab_ca_ba,(P,Q,R)), body_literal(Rule,P,_,(A,B)), body_literal(Rule,Q,_,(C,A)), body_literal(Rule,R,_,(B,A)).
:- prop(ab_ca_ba,(P,Q,R)), body_literal(Rule,P,_,(A,B)), body_literal(Rule,Q,_,(C,A)), body_literal(Rule,R,_,(B,A)), valid_var(Rule,B),valid_var(Rule,A).
:- prop(not_ab_ca_ca,(P,Q,R)), body_literal(Rule,P,_,(A,B)), body_literal(Rule,Q,_,(C,A)), body_literal(Rule,R,_,(C,A)).
:- prop(ab_ca_ca,(P,Q,R)), body_literal(Rule,P,_,(A,B)), body_literal(Rule,Q,_,(C,A)), body_literal(Rule,R,_,(C,A)), valid_var(Rule,C),valid_var(Rule,A).
:- prop(not_ab_ac_a,(P,Q,R)), body_literal(Rule,P,_,(A,B)), body_literal(Rule,Q,_,(A,C)), body_literal(Rule,R,_,(A,)).
:- prop(ab_ac_a,(P,Q,R)), body_literal(Rule,P,_,(A,B)), body_literal(Rule,Q,_,(A,C)), body_literal(Rule,R,_,(A,)), valid_var(Rule,A).
:- prop(not_ab_a_b,(P,Q,R)), body_literal(Rule,P,_,(A,B)), body_literal(Rule,Q,_,(A,)), body_literal(Rule,R,_,(B,)).
:- prop(ab_a_b,(P,Q,R)), body_literal(Rule,P,_,(A,B)), body_literal(Rule,Q,_,(A,)), body_literal(Rule,R,_,(B,)), valid_var(Rule,B).
:- prop(not_ab_ab_ab,(P,Q,R)), body_literal(Rule,P,_,(A,B)), body_literal(Rule,Q,_,(A,B)), body_literal(Rule,R,_,(A,B)).
:- prop(ab_ab_ab,(P,Q,R)), body_literal(Rule,P,_,(A,B)), body_literal(Rule,Q,_,(A,B)), body_literal(Rule,R,_,(A,B)), valid_var(Rule,B),valid_var(Rule,A).
:- prop(not_ab_ac_b,(P,Q,R)), body_literal(Rule,P,_,(A,B)), body_literal(Rule,Q,_,(A,C)), body_literal(Rule,R,_,(B,)).
:- prop(ab_ac_b,(P,Q,R)), body_literal(Rule,P,_,(A,B)), body_literal(Rule,Q,_,(A,C)), body_literal(Rule,R,_,(B,)), valid_var(Rule,B).
:- prop(not_ab_bc_a,(P,Q,R)), body_literal(Rule,P,_,(A,B)), body_literal(Rule,Q,_,(B,C)), body_literal(Rule,R,_,(A,)).
:- prop(ab_bc_a,(P,Q,R)), body_literal(Rule,P,_,(A,B)), body_literal(Rule,Q,_,(B,C)), body_literal(Rule,R,_,(A,)), valid_var(Rule,A).
:- prop(not_ab_ca_cb,(P,Q,R)), body_literal(Rule,P,_,(A,B)), body_literal(Rule,Q,_,(C,A)), body_literal(Rule,R,_,(C,B)).
:- prop(ab_ca_cb,(P,Q,R)), body_literal(Rule,P,_,(A,B)), body_literal(Rule,Q,_,(C,A)), body_literal(Rule,R,_,(C,B)), valid_var(Rule,B),valid_var(Rule,C).
:- prop(not_ab_ab_bc,(P,Q,R)), body_literal(Rule,P,_,(A,B)), body_literal(Rule,Q,_,(A,B)), body_literal(Rule,R,_,(B,C)).
:- prop(not_ab_bc_b,(P,Q,R)), body_literal(Rule,P,_,(A,B)), body_literal(Rule,Q,_,(B,C)), body_literal(Rule,R,_,(B,)).
:- prop(ab_bc_b,(P,Q,R)), body_literal(Rule,P,_,(A,B)), body_literal(Rule,Q,_,(B,C)), body_literal(Rule,R,_,(B,)), valid_var(Rule,B).
:- prop(not_ab_ba_cb,(P,Q,R)), body_literal(Rule,P,_,(A,B)), body_literal(Rule,Q,_,(B,A)), body_literal(Rule,R,_,(C,B)).
:- prop(not_ab_ca_a,(P,Q,R)), body_literal(Rule,P,_,(A,B)), body_literal(Rule,Q,_,(C,A)), body_literal(Rule,R,_,(A,)).
:- prop(ab_ca_a,(P,Q,R)), body_literal(Rule,P,_,(A,B)), body_literal(Rule,Q,_,(C,A)), body_literal(Rule,R,_,(A,)), valid_var(Rule,A).
:- prop(not_a_a_a,(P,Q,R)), body_literal(Rule,P,_,(A,)), body_literal(Rule,Q,_,(A,)), body_literal(Rule,R,_,(A,)).
:- prop(a_a_a,(P,Q,R)), body_literal(Rule,P,_,(A,)), body_literal(Rule,Q,_,(A,)), body_literal(Rule,R,_,(A,)), valid_var(Rule,A).
:- prop(not_ab_ca_b,(P,Q,R)), body_literal(Rule,P,_,(A,B)), body_literal(Rule,Q,_,(C,A)), body_literal(Rule,R,_,(B,)).
:- prop(ab_ca_b,(P,Q,R)), body_literal(Rule,P,_,(A,B)), body_literal(Rule,Q,_,(C,A)), body_literal(Rule,R,_,(B,)), valid_var(Rule,B).
:- prop(not_ab_ba_a,(P,Q,R)), body_literal(Rule,P,_,(A,B)), body_literal(Rule,Q,_,(B,A)), body_literal(Rule,R,_,(A,)).
:- prop(ab_ba_a,(P,Q,R)), body_literal(Rule,P,_,(A,B)), body_literal(Rule,Q,_,(B,A)), body_literal(Rule,R,_,(A,)), valid_var(Rule,A).
:- prop(not_ab_cb_c,(P,Q,R)), body_literal(Rule,P,_,(A,B)), body_literal(Rule,Q,_,(C,B)), body_literal(Rule,R,_,(C,)).
:- prop(ab_cb_c,(P,Q,R)), body_literal(Rule,P,_,(A,B)), body_literal(Rule,Q,_,(C,B)), body_literal(Rule,R,_,(C,)), valid_var(Rule,C).
:- prop(not_ab_ba_b,(P,Q,R)), body_literal(Rule,P,_,(A,B)), body_literal(Rule,Q,_,(B,A)), body_literal(Rule,R,_,(B,)).
:- prop(ab_ba_b,(P,Q,R)), body_literal(Rule,P,_,(A,B)), body_literal(Rule,Q,_,(B,A)), body_literal(Rule,R,_,(B,)), valid_var(Rule,B).

#heuristic size(N). [1000-N,true]

NO SOLUTION
