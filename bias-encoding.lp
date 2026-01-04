(':- clause(C), #count{V : var_type(C, V,a_tid)} > 2.', ':- clause(C), #count{V : var_type(C, V,authors)} > 6.', ':- clause(C), #count{V : var_type(C, V,d_tid)} > 2.', ':- clause(C), #count{V : var_type(C, V,did)} > 2.', ':- clause(C), #count{V : var_type(C, V,title)} > 6.', ':- clause(C), #count{V : var_type(C, V,aid)} > 2.')
type_pos((did, aid), 0, did).
type_pos((did, aid), 1, aid).
type_pos((d_tid, did), 0, d_tid).
type_pos((d_tid, did), 1, did).
type_pos((a_tid, aid), 0, a_tid).
type_pos((a_tid, aid), 1, aid).
type_pos((d_tid, title), 0, d_tid).
type_pos((d_tid, title), 1, title).
type_pos((a_tid, title), 0, a_tid).
type_pos((a_tid, title), 1, title).
type_pos((d_tid, authors), 0, d_tid).
type_pos((d_tid, authors), 1, authors).
type_pos((a_tid, authors), 0, a_tid).
type_pos((a_tid, authors), 1, authors).
type_pos((title, title), 0, title).
type_pos((title, title), 1, title).
type_pos((authors, authors), 0, authors).
type_pos((authors, authors), 1, authors).
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
    body_literal(C,_,_,Vars),
    var_member(Var,Vars).

%% VAR IN A TUPLE OF VARS
var_member(Var,Vars):-
    var_pos(Var,Vars,_).

%% ##################################################
%% BIAS CONSTRAINTS
%% ##################################################
%% DATALOG
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
:-
    head_literal(C,_,A,_),
    Var >= A,
    body_var(C,Var),
    not head_connected(C,Var).

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
schema(dblp_acm).
r(dblp_acm,dblp,6).
r(dblp_acm,acm,6).

% er_type: 4 - default, 2 - object, 3 - value, 0 - tid
attr(a0,tid,dblp,0,4).
attr(a1,id,dblp,1,2).
attr(a2,title,dblp,2,4).
attr(a3,authors,dblp,3,4).

attr(a11,tid,acm,0,4).
attr(a6,id,acm,1,2).
attr(a7,title,acm,2,4).
attr(a8,authors,acm,3,4).


compatible_attr(a1,a6).
compatible_attr(a2,a7).
compatible_attr(a3,a8).
compatible_attr(a4,a9).
compatible_attr(a5,a10).


head_pred(eqo,2).
% head_pred(eqv,4).

body_pred(sim,2).

body_pred(dblp_title,2).
body_pred(acm_title,2).
body_pred(dblp_id,2).
body_pred(acm_id,2).
body_pred(dblp_authors,2).
body_pred(acm_authors,2).
%body_pred(dblp_year,2).
%body_pred(acm_year,2).


type(dblp_id,(d_tid,did)).
type(acm_id,(a_tid,aid)).
type(dblp_title,(d_tid,title)).
type(acm_title,(a_tid,title)).
type(dblp_authors,(d_tid,authors)).
type(acm_authors,(a_tid,authors)).
%type(dblp_year,(d_tid,year)).
%type(acm_year,(a_tid,year)).

type(sim,(title,title)).
type(sim,(authors,authors)).


type(eqo,(did,aid)).
% type(eqv,(d_tid,did,a_tid,aid)).



max_clauses(1).
max_body(10).
max_vars(10).
head_vars(2, (0, 1)).
vars(2, (0, 1)).
var_pos(0, (0, 1), 0).
var_pos(1, (0, 1), 1).
ordered_vars((0, 1),(0, 1)).
vars(2, (0, 2)).
var_pos(0, (0, 2), 0).
var_pos(2, (0, 2), 1).
ordered_vars((0, 2),(0, 2)).
vars(2, (0, 3)).
var_pos(0, (0, 3), 0).
var_pos(3, (0, 3), 1).
ordered_vars((0, 3),(0, 3)).
vars(2, (0, 4)).
var_pos(0, (0, 4), 0).
var_pos(4, (0, 4), 1).
ordered_vars((0, 4),(0, 4)).
vars(2, (0, 5)).
var_pos(0, (0, 5), 0).
var_pos(5, (0, 5), 1).
ordered_vars((0, 5),(0, 5)).
vars(2, (0, 6)).
var_pos(0, (0, 6), 0).
var_pos(6, (0, 6), 1).
ordered_vars((0, 6),(0, 6)).
vars(2, (0, 7)).
var_pos(0, (0, 7), 0).
var_pos(7, (0, 7), 1).
ordered_vars((0, 7),(0, 7)).
vars(2, (0, 8)).
var_pos(0, (0, 8), 0).
var_pos(8, (0, 8), 1).
ordered_vars((0, 8),(0, 8)).
vars(2, (0, 9)).
var_pos(0, (0, 9), 0).
var_pos(9, (0, 9), 1).
ordered_vars((0, 9),(0, 9)).
vars(2, (1, 0)).
var_pos(1, (1, 0), 0).
var_pos(0, (1, 0), 1).
ordered_vars((1, 0),(0, 1)).
vars(2, (1, 2)).
var_pos(1, (1, 2), 0).
var_pos(2, (1, 2), 1).
ordered_vars((1, 2),(1, 2)).
vars(2, (1, 3)).
var_pos(1, (1, 3), 0).
var_pos(3, (1, 3), 1).
ordered_vars((1, 3),(1, 3)).
vars(2, (1, 4)).
var_pos(1, (1, 4), 0).
var_pos(4, (1, 4), 1).
ordered_vars((1, 4),(1, 4)).
vars(2, (1, 5)).
var_pos(1, (1, 5), 0).
var_pos(5, (1, 5), 1).
ordered_vars((1, 5),(1, 5)).
vars(2, (1, 6)).
var_pos(1, (1, 6), 0).
var_pos(6, (1, 6), 1).
ordered_vars((1, 6),(1, 6)).
vars(2, (1, 7)).
var_pos(1, (1, 7), 0).
var_pos(7, (1, 7), 1).
ordered_vars((1, 7),(1, 7)).
vars(2, (1, 8)).
var_pos(1, (1, 8), 0).
var_pos(8, (1, 8), 1).
ordered_vars((1, 8),(1, 8)).
vars(2, (1, 9)).
var_pos(1, (1, 9), 0).
var_pos(9, (1, 9), 1).
ordered_vars((1, 9),(1, 9)).
vars(2, (2, 0)).
var_pos(2, (2, 0), 0).
var_pos(0, (2, 0), 1).
ordered_vars((2, 0),(0, 2)).
vars(2, (2, 1)).
var_pos(2, (2, 1), 0).
var_pos(1, (2, 1), 1).
ordered_vars((2, 1),(1, 2)).
vars(2, (2, 3)).
var_pos(2, (2, 3), 0).
var_pos(3, (2, 3), 1).
ordered_vars((2, 3),(2, 3)).
vars(2, (2, 4)).
var_pos(2, (2, 4), 0).
var_pos(4, (2, 4), 1).
ordered_vars((2, 4),(2, 4)).
vars(2, (2, 5)).
var_pos(2, (2, 5), 0).
var_pos(5, (2, 5), 1).
ordered_vars((2, 5),(2, 5)).
vars(2, (2, 6)).
var_pos(2, (2, 6), 0).
var_pos(6, (2, 6), 1).
ordered_vars((2, 6),(2, 6)).
vars(2, (2, 7)).
var_pos(2, (2, 7), 0).
var_pos(7, (2, 7), 1).
ordered_vars((2, 7),(2, 7)).
vars(2, (2, 8)).
var_pos(2, (2, 8), 0).
var_pos(8, (2, 8), 1).
ordered_vars((2, 8),(2, 8)).
vars(2, (2, 9)).
var_pos(2, (2, 9), 0).
var_pos(9, (2, 9), 1).
ordered_vars((2, 9),(2, 9)).
vars(2, (3, 0)).
var_pos(3, (3, 0), 0).
var_pos(0, (3, 0), 1).
ordered_vars((3, 0),(0, 3)).
vars(2, (3, 1)).
var_pos(3, (3, 1), 0).
var_pos(1, (3, 1), 1).
ordered_vars((3, 1),(1, 3)).
vars(2, (3, 2)).
var_pos(3, (3, 2), 0).
var_pos(2, (3, 2), 1).
ordered_vars((3, 2),(2, 3)).
vars(2, (3, 4)).
var_pos(3, (3, 4), 0).
var_pos(4, (3, 4), 1).
ordered_vars((3, 4),(3, 4)).
vars(2, (3, 5)).
var_pos(3, (3, 5), 0).
var_pos(5, (3, 5), 1).
ordered_vars((3, 5),(3, 5)).
vars(2, (3, 6)).
var_pos(3, (3, 6), 0).
var_pos(6, (3, 6), 1).
ordered_vars((3, 6),(3, 6)).
vars(2, (3, 7)).
var_pos(3, (3, 7), 0).
var_pos(7, (3, 7), 1).
ordered_vars((3, 7),(3, 7)).
vars(2, (3, 8)).
var_pos(3, (3, 8), 0).
var_pos(8, (3, 8), 1).
ordered_vars((3, 8),(3, 8)).
vars(2, (3, 9)).
var_pos(3, (3, 9), 0).
var_pos(9, (3, 9), 1).
ordered_vars((3, 9),(3, 9)).
vars(2, (4, 0)).
var_pos(4, (4, 0), 0).
var_pos(0, (4, 0), 1).
ordered_vars((4, 0),(0, 4)).
vars(2, (4, 1)).
var_pos(4, (4, 1), 0).
var_pos(1, (4, 1), 1).
ordered_vars((4, 1),(1, 4)).
vars(2, (4, 2)).
var_pos(4, (4, 2), 0).
var_pos(2, (4, 2), 1).
ordered_vars((4, 2),(2, 4)).
vars(2, (4, 3)).
var_pos(4, (4, 3), 0).
var_pos(3, (4, 3), 1).
ordered_vars((4, 3),(3, 4)).
vars(2, (4, 5)).
var_pos(4, (4, 5), 0).
var_pos(5, (4, 5), 1).
ordered_vars((4, 5),(4, 5)).
vars(2, (4, 6)).
var_pos(4, (4, 6), 0).
var_pos(6, (4, 6), 1).
ordered_vars((4, 6),(4, 6)).
vars(2, (4, 7)).
var_pos(4, (4, 7), 0).
var_pos(7, (4, 7), 1).
ordered_vars((4, 7),(4, 7)).
vars(2, (4, 8)).
var_pos(4, (4, 8), 0).
var_pos(8, (4, 8), 1).
ordered_vars((4, 8),(4, 8)).
vars(2, (4, 9)).
var_pos(4, (4, 9), 0).
var_pos(9, (4, 9), 1).
ordered_vars((4, 9),(4, 9)).
vars(2, (5, 0)).
var_pos(5, (5, 0), 0).
var_pos(0, (5, 0), 1).
ordered_vars((5, 0),(0, 5)).
vars(2, (5, 1)).
var_pos(5, (5, 1), 0).
var_pos(1, (5, 1), 1).
ordered_vars((5, 1),(1, 5)).
vars(2, (5, 2)).
var_pos(5, (5, 2), 0).
var_pos(2, (5, 2), 1).
ordered_vars((5, 2),(2, 5)).
vars(2, (5, 3)).
var_pos(5, (5, 3), 0).
var_pos(3, (5, 3), 1).
ordered_vars((5, 3),(3, 5)).
vars(2, (5, 4)).
var_pos(5, (5, 4), 0).
var_pos(4, (5, 4), 1).
ordered_vars((5, 4),(4, 5)).
vars(2, (5, 6)).
var_pos(5, (5, 6), 0).
var_pos(6, (5, 6), 1).
ordered_vars((5, 6),(5, 6)).
vars(2, (5, 7)).
var_pos(5, (5, 7), 0).
var_pos(7, (5, 7), 1).
ordered_vars((5, 7),(5, 7)).
vars(2, (5, 8)).
var_pos(5, (5, 8), 0).
var_pos(8, (5, 8), 1).
ordered_vars((5, 8),(5, 8)).
vars(2, (5, 9)).
var_pos(5, (5, 9), 0).
var_pos(9, (5, 9), 1).
ordered_vars((5, 9),(5, 9)).
vars(2, (6, 0)).
var_pos(6, (6, 0), 0).
var_pos(0, (6, 0), 1).
ordered_vars((6, 0),(0, 6)).
vars(2, (6, 1)).
var_pos(6, (6, 1), 0).
var_pos(1, (6, 1), 1).
ordered_vars((6, 1),(1, 6)).
vars(2, (6, 2)).
var_pos(6, (6, 2), 0).
var_pos(2, (6, 2), 1).
ordered_vars((6, 2),(2, 6)).
vars(2, (6, 3)).
var_pos(6, (6, 3), 0).
var_pos(3, (6, 3), 1).
ordered_vars((6, 3),(3, 6)).
vars(2, (6, 4)).
var_pos(6, (6, 4), 0).
var_pos(4, (6, 4), 1).
ordered_vars((6, 4),(4, 6)).
vars(2, (6, 5)).
var_pos(6, (6, 5), 0).
var_pos(5, (6, 5), 1).
ordered_vars((6, 5),(5, 6)).
vars(2, (6, 7)).
var_pos(6, (6, 7), 0).
var_pos(7, (6, 7), 1).
ordered_vars((6, 7),(6, 7)).
vars(2, (6, 8)).
var_pos(6, (6, 8), 0).
var_pos(8, (6, 8), 1).
ordered_vars((6, 8),(6, 8)).
vars(2, (6, 9)).
var_pos(6, (6, 9), 0).
var_pos(9, (6, 9), 1).
ordered_vars((6, 9),(6, 9)).
vars(2, (7, 0)).
var_pos(7, (7, 0), 0).
var_pos(0, (7, 0), 1).
ordered_vars((7, 0),(0, 7)).
vars(2, (7, 1)).
var_pos(7, (7, 1), 0).
var_pos(1, (7, 1), 1).
ordered_vars((7, 1),(1, 7)).
vars(2, (7, 2)).
var_pos(7, (7, 2), 0).
var_pos(2, (7, 2), 1).
ordered_vars((7, 2),(2, 7)).
vars(2, (7, 3)).
var_pos(7, (7, 3), 0).
var_pos(3, (7, 3), 1).
ordered_vars((7, 3),(3, 7)).
vars(2, (7, 4)).
var_pos(7, (7, 4), 0).
var_pos(4, (7, 4), 1).
ordered_vars((7, 4),(4, 7)).
vars(2, (7, 5)).
var_pos(7, (7, 5), 0).
var_pos(5, (7, 5), 1).
ordered_vars((7, 5),(5, 7)).
vars(2, (7, 6)).
var_pos(7, (7, 6), 0).
var_pos(6, (7, 6), 1).
ordered_vars((7, 6),(6, 7)).
vars(2, (7, 8)).
var_pos(7, (7, 8), 0).
var_pos(8, (7, 8), 1).
ordered_vars((7, 8),(7, 8)).
vars(2, (7, 9)).
var_pos(7, (7, 9), 0).
var_pos(9, (7, 9), 1).
ordered_vars((7, 9),(7, 9)).
vars(2, (8, 0)).
var_pos(8, (8, 0), 0).
var_pos(0, (8, 0), 1).
ordered_vars((8, 0),(0, 8)).
vars(2, (8, 1)).
var_pos(8, (8, 1), 0).
var_pos(1, (8, 1), 1).
ordered_vars((8, 1),(1, 8)).
vars(2, (8, 2)).
var_pos(8, (8, 2), 0).
var_pos(2, (8, 2), 1).
ordered_vars((8, 2),(2, 8)).
vars(2, (8, 3)).
var_pos(8, (8, 3), 0).
var_pos(3, (8, 3), 1).
ordered_vars((8, 3),(3, 8)).
vars(2, (8, 4)).
var_pos(8, (8, 4), 0).
var_pos(4, (8, 4), 1).
ordered_vars((8, 4),(4, 8)).
vars(2, (8, 5)).
var_pos(8, (8, 5), 0).
var_pos(5, (8, 5), 1).
ordered_vars((8, 5),(5, 8)).
vars(2, (8, 6)).
var_pos(8, (8, 6), 0).
var_pos(6, (8, 6), 1).
ordered_vars((8, 6),(6, 8)).
vars(2, (8, 7)).
var_pos(8, (8, 7), 0).
var_pos(7, (8, 7), 1).
ordered_vars((8, 7),(7, 8)).
vars(2, (8, 9)).
var_pos(8, (8, 9), 0).
var_pos(9, (8, 9), 1).
ordered_vars((8, 9),(8, 9)).
vars(2, (9, 0)).
var_pos(9, (9, 0), 0).
var_pos(0, (9, 0), 1).
ordered_vars((9, 0),(0, 9)).
vars(2, (9, 1)).
var_pos(9, (9, 1), 0).
var_pos(1, (9, 1), 1).
ordered_vars((9, 1),(1, 9)).
vars(2, (9, 2)).
var_pos(9, (9, 2), 0).
var_pos(2, (9, 2), 1).
ordered_vars((9, 2),(2, 9)).
vars(2, (9, 3)).
var_pos(9, (9, 3), 0).
var_pos(3, (9, 3), 1).
ordered_vars((9, 3),(3, 9)).
vars(2, (9, 4)).
var_pos(9, (9, 4), 0).
var_pos(4, (9, 4), 1).
ordered_vars((9, 4),(4, 9)).
vars(2, (9, 5)).
var_pos(9, (9, 5), 0).
var_pos(5, (9, 5), 1).
ordered_vars((9, 5),(5, 9)).
vars(2, (9, 6)).
var_pos(9, (9, 6), 0).
var_pos(6, (9, 6), 1).
ordered_vars((9, 6),(6, 9)).
vars(2, (9, 7)).
var_pos(9, (9, 7), 0).
var_pos(7, (9, 7), 1).
ordered_vars((9, 7),(7, 9)).
vars(2, (9, 8)).
var_pos(9, (9, 8), 0).
var_pos(8, (9, 8), 1).
ordered_vars((9, 8),(8, 9)).
appears((V0,V1)):- body_literal(_,_,_,(X0,X1)), ordered_vars((X0,X1), (V0,V1)).
var_tuple((V0,V1)):- body_pred(P,2), vars(2,Vars), not bad_body(P,Vars), not type_mismatch(P,Vars), ordered_vars(Vars,OrderedVars), OrderedVars=(V0,V1).
var_member(V,(V0,V1)):-vars(_, Vars), Vars=(V0,V1), var_member(V,Vars).
lower((V0,V1),(X0,X1)):- var_tuple((V0,V1)), var_tuple((X0,X1)), X0 < V0.
lower((V0,V1),(V0,X1)):- var_tuple((V0,V1)), var_tuple((V0,X1)), X1 < V1.
seen_lower(Vars1, V):- V=V1-1, Vars1 = (V0,V1), V0 < V < V1, lower(Vars1, Vars2), var_tuple(Vars1), appears(Vars2), var_member(V, Vars2), not head_var(_,V).
gap_((V0,V1),V1-1):- var_tuple((V0,V1)), V0 < V < V1, var(V).
gap((V0,V1),V):- gap_((V0,V1), _), #max{X :gap_((V0,V1), X)} == V.
:- appears((V0,V1)), gap((V0,V1), V), not seen_lower((V0,V1),V), not head_var(_,V).
type_pos((d_tid, authors), 1, authors).
type_pos((d_tid, title), 0, d_tid).
type_pos((d_tid, authors), 0, d_tid).
type_pos((d_tid, title), 1, title).
type_pos((did, aid), 0, did).
type_pos((a_tid, title), 0, a_tid).
type_pos((title, title), 1, title).
type_pos((a_tid, aid), 0, a_tid).
type_pos((d_tid, did), 0, d_tid).
type_pos((title, title), 0, title).
type_pos((did, aid), 1, aid).
type_pos((d_tid, did), 1, did).
type_pos((a_tid, authors), 1, authors).
type_pos((a_tid, aid), 1, aid).
type_pos((a_tid, authors), 0, a_tid).
type_pos((a_tid, title), 1, title).
type_pos((authors, authors), 1, authors).
type_pos((authors, authors), 0, authors).
:- body_literal(Rule,acm_authors,_,(_,_)), #count{V0,V1: body_literal(Rule,acm_authors,_,(V0,V1))} > 2.
:- body_literal(Rule,acm_authors,_,(_,V1)), #count{V0: body_literal(Rule,acm_authors,_,(V0,V1))} > 1.
:- body_literal(Rule,acm_authors,_,(V0,_)), #count{V1: body_literal(Rule,acm_authors,_,(V0,V1))} > 1.
:- body_literal(Rule,dblp_id,_,(_,_)), #count{V0,V1: body_literal(Rule,dblp_id,_,(V0,V1))} > 2.
:- body_literal(Rule,dblp_id,_,(_,V1)), #count{V0: body_literal(Rule,dblp_id,_,(V0,V1))} > 1.
:- body_literal(Rule,dblp_id,_,(V0,_)), #count{V1: body_literal(Rule,dblp_id,_,(V0,V1))} > 1.
:- body_literal(Rule,sim,_,(_,_)), #count{V0,V1: body_literal(Rule,sim,_,(V0,V1))} > 4.
:- body_literal(Rule,sim,_,(_,V1)), #count{V0: body_literal(Rule,sim,_,(V0,V1))} > 1.
:- body_literal(Rule,sim,_,(V0,_)), #count{V1: body_literal(Rule,sim,_,(V0,V1))} > 1.
:- body_literal(Rule,dblp_title,_,(_,_)), #count{V0,V1: body_literal(Rule,dblp_title,_,(V0,V1))} > 2.
:- body_literal(Rule,dblp_title,_,(_,V1)), #count{V0: body_literal(Rule,dblp_title,_,(V0,V1))} > 1.
:- body_literal(Rule,dblp_title,_,(V0,_)), #count{V1: body_literal(Rule,dblp_title,_,(V0,V1))} > 1.
:- body_literal(Rule,acm_title,_,(_,_)), #count{V0,V1: body_literal(Rule,acm_title,_,(V0,V1))} > 2.
:- body_literal(Rule,acm_title,_,(_,V1)), #count{V0: body_literal(Rule,acm_title,_,(V0,V1))} > 1.
:- body_literal(Rule,acm_title,_,(V0,_)), #count{V1: body_literal(Rule,acm_title,_,(V0,V1))} > 1.
:- body_literal(Rule,dblp_authors,_,(_,_)), #count{V0,V1: body_literal(Rule,dblp_authors,_,(V0,V1))} > 2.
:- body_literal(Rule,dblp_authors,_,(_,V1)), #count{V0: body_literal(Rule,dblp_authors,_,(V0,V1))} > 1.
:- body_literal(Rule,dblp_authors,_,(V0,_)), #count{V1: body_literal(Rule,dblp_authors,_,(V0,V1))} > 1.
:- body_literal(Rule,acm_id,_,(_,_)), #count{V0,V1: body_literal(Rule,acm_id,_,(V0,V1))} > 2.
:- body_literal(Rule,acm_id,_,(_,V1)), #count{V0: body_literal(Rule,acm_id,_,(V0,V1))} > 1.
:- body_literal(Rule,acm_id,_,(V0,_)), #count{V1: body_literal(Rule,acm_id,_,(V0,V1))} > 1.
:- body_literal(_, acm_authors, _, (V0,V1)), singleton(V1).
:- body_literal(_, acm_id, _, (V0,V1)), singleton(V1).
:- body_literal(_, acm_id, _, (V0,V1)), singleton(V0).
:- body_literal(_, acm_title, _, (V0,V1)), singleton(V1).
:- body_literal(_, dblp_authors, _, (V0,V1)), singleton(V1).
:- body_literal(_, dblp_id, _, (V0,V1)), singleton(V1).
:- body_literal(_, dblp_id, _, (V0,V1)), singleton(V0).
:- body_literal(_, dblp_title, _, (V0,V1)), singleton(V1).
:- clause(C), #count{V : var_type(C, V,a_tid)} > 2.
:- clause(C), #count{V : var_type(C, V,authors)} > 6.
:- clause(C), #count{V : var_type(C, V,d_tid)} > 2.
:- clause(C), #count{V : var_type(C, V,did)} > 2.
:- clause(C), #count{V : var_type(C, V,title)} > 6.
:- clause(C), #count{V : var_type(C, V,aid)} > 2.
prop(not_ab_ca_db,(sim,acm_authors,acm_authors)).
prop(not_ab_cb_ca,(sim,dblp_title,dblp_title)).
prop(not_ab_cb_ca,(sim,acm_title,acm_title)).
prop(not_ab_bc_ca,(sim,sim,sim)).
prop(not_ab_bc_dc,(acm_title,sim,acm_title)).
prop(not_ab_cb_da,(sim,acm_title,acm_title)).
prop(not_ab_cb_dc,(acm_title,sim,acm_title)).
prop(not_ab_ca_db,(sim,dblp_authors,dblp_authors)).
prop(ab_ba,(sim,sim)).
prop(not_ab_ac_bc,(acm_authors,acm_authors,sim)).
prop(ab_ca_ac,(sim,sim,sim)).
prop(not_ab_cb,(dblp_authors,acm_authors)).
prop(not_ab_ca_db,(sim,acm_title,acm_title)).
prop(not_ab_ca_db,(sim,dblp_title,dblp_title)).
prop(not_ab_cb,(acm_authors,dblp_authors)).
prop(ab_bc_cb,(sim,sim,sim)).
prop(not_ab_ac_cb,(dblp_title,dblp_title,sim)).
prop(not_ab_ac_bc,(acm_title,acm_title,sim)).
prop(not_ab_bc_dc,(dblp_title,sim,dblp_title)).
prop(not_ab_bc_dc,(dblp_authors,sim,dblp_authors)).
prop(ab_bc_cb,(acm_title,sim,sim)).
prop(not_ab_cb_ca,(sim,sim,sim)).
prop(not_ab_ac_bc,(sim,sim,sim)).
prop(ab_bc_cb,(dblp_title,sim,sim)).
prop(not_ab_ac_bc,(dblp_authors,dblp_authors,sim)).
prop(not_ab_ac_bc,(dblp_title,dblp_title,sim)).
prop(not_ab_cb,(dblp_title,acm_title)).
prop(not_ab_cb_ca,(sim,dblp_authors,dblp_authors)).
prop(not_ab_ac_cb,(sim,sim,sim)).
prop(not_ab_ac_cb,(dblp_authors,dblp_authors,sim)).
prop(not_ab_cb_da,(sim,dblp_authors,dblp_authors)).
prop(ab_bc_cb,(dblp_authors,sim,sim)).
prop(not_ab_cb_da,(sim,dblp_title,dblp_title)).
prop(not_ab_bc_dc,(acm_authors,sim,acm_authors)).
prop(ab_bc_cb,(acm_authors,sim,sim)).
prop(not_ab_ac_cb,(acm_authors,acm_authors,sim)).
prop(not_ab_cb,(acm_title,dblp_title)).
prop(not_ab_cb_dc,(dblp_title,sim,dblp_title)).
prop(not_ab_cb_ca,(sim,acm_authors,acm_authors)).
prop(not_ab_ac_cb,(acm_title,acm_title,sim)).
prop(not_ab_cb_dc,(dblp_authors,sim,dblp_authors)).
prop(not_ab_cb_da,(sim,acm_authors,acm_authors)).
prop(not_ab_cb_dc,(acm_authors,sim,acm_authors)).
:- prop(not_ab_ab,(P,Q)), body_literal(Rule,P,_,(A,B)), body_literal(Rule,Q,_,(A,B)).
:- prop(ab_ab,(P,Q)), body_literal(Rule,P,_,(A,B)), body_literal(Rule,Q,_,(A,B)), valid_var(Rule,A),valid_var(Rule,B).
:- prop(not_ab_bc,(P,Q)), body_literal(Rule,P,_,(A,B)), body_literal(Rule,Q,_,(B,_)).
:- prop(not_ab_cb,(P,Q)), body_literal(Rule,P,_,(A,B)), body_literal(Rule,Q,_,(_,B)).
:- prop(not_ab_ca,(P,Q)), body_literal(Rule,P,_,(A,B)), body_literal(Rule,Q,_,(_,A)).
:- prop(not_ab_ba,(P,Q)), body_literal(Rule,P,_,(A,B)), body_literal(Rule,Q,_,(B,A)).
:- prop(ab_ba,(P,Q)), body_literal(Rule,P,_,(A,B)), body_literal(Rule,Q,_,(B,A)), valid_var(Rule,A),valid_var(Rule,B).
:- prop(not_ab_ac,(P,Q)), body_literal(Rule,P,_,(A,B)), body_literal(Rule,Q,_,(A,_)).
:- prop(not_ab_ba_ca,(P,Q,R)), body_literal(Rule,P,_,(A,B)), body_literal(Rule,Q,_,(B,A)), body_literal(Rule,R,_,(C,A)).
:- prop(not_ab_ba_ac,(P,Q,R)), body_literal(Rule,P,_,(A,B)), body_literal(Rule,Q,_,(B,A)), body_literal(Rule,R,_,(A,C)).
:- prop(not_ab_bc_cd,(P,Q,R)), body_literal(Rule,P,_,(A,B)), body_literal(Rule,Q,_,(B,C)), body_literal(Rule,R,_,(C,D)).
:- prop(not_ab_ac_ab,(P,Q,R)), body_literal(Rule,P,_,(A,B)), body_literal(Rule,Q,_,(A,C)), body_literal(Rule,R,_,(A,B)).
:- prop(ab_ac_ab,(P,Q,R)), body_literal(Rule,P,_,(A,B)), body_literal(Rule,Q,_,(A,C)), body_literal(Rule,R,_,(A,B)), valid_var(Rule,A),valid_var(Rule,B).
:- prop(not_ab_ca_ca,(P,Q,R)), body_literal(Rule,P,_,(A,B)), body_literal(Rule,Q,_,(C,A)), body_literal(Rule,R,_,(C,A)).
:- prop(ab_ca_ca,(P,Q,R)), body_literal(Rule,P,_,(A,B)), body_literal(Rule,Q,_,(C,A)), body_literal(Rule,R,_,(C,A)), valid_var(Rule,A),valid_var(Rule,C).
:- prop(not_ab_ac_bc,(P,Q,R)), body_literal(Rule,P,_,(A,B)), body_literal(Rule,Q,_,(A,C)), body_literal(Rule,R,_,(B,C)).
:- prop(ab_ac_bc,(P,Q,R)), body_literal(Rule,P,_,(A,B)), body_literal(Rule,Q,_,(A,C)), body_literal(Rule,R,_,(B,C)), valid_var(Rule,C),valid_var(Rule,B).
:- prop(not_ab_ca_ac,(P,Q,R)), body_literal(Rule,P,_,(A,B)), body_literal(Rule,Q,_,(C,A)), body_literal(Rule,R,_,(A,C)).
:- prop(ab_ca_ac,(P,Q,R)), body_literal(Rule,P,_,(A,B)), body_literal(Rule,Q,_,(C,A)), body_literal(Rule,R,_,(A,C)), valid_var(Rule,A),valid_var(Rule,C).
:- prop(not_ab_ca_bd,(P,Q,R)), body_literal(Rule,P,_,(A,B)), body_literal(Rule,Q,_,(C,A)), body_literal(Rule,R,_,(B,D)).
:- prop(not_ab_bc_bd,(P,Q,R)), body_literal(Rule,P,_,(A,B)), body_literal(Rule,Q,_,(B,C)), body_literal(Rule,R,_,(B,D)).
:- prop(not_ab_bc_ca,(P,Q,R)), body_literal(Rule,P,_,(A,B)), body_literal(Rule,Q,_,(B,C)), body_literal(Rule,R,_,(C,A)).
:- prop(ab_bc_ca,(P,Q,R)), body_literal(Rule,P,_,(A,B)), body_literal(Rule,Q,_,(B,C)), body_literal(Rule,R,_,(C,A)), valid_var(Rule,A),valid_var(Rule,C).
:- prop(not_ab_ca_da,(P,Q,R)), body_literal(Rule,P,_,(A,B)), body_literal(Rule,Q,_,(C,A)), body_literal(Rule,R,_,(D,A)).
:- prop(not_ab_bc_da,(P,Q,R)), body_literal(Rule,P,_,(A,B)), body_literal(Rule,Q,_,(B,C)), body_literal(Rule,R,_,(D,A)).
:- prop(not_ab_ab_ab,(P,Q,R)), body_literal(Rule,P,_,(A,B)), body_literal(Rule,Q,_,(A,B)), body_literal(Rule,R,_,(A,B)).
:- prop(ab_ab_ab,(P,Q,R)), body_literal(Rule,P,_,(A,B)), body_literal(Rule,Q,_,(A,B)), body_literal(Rule,R,_,(A,B)), valid_var(Rule,A),valid_var(Rule,B).
:- prop(not_ab_ab_bc,(P,Q,R)), body_literal(Rule,P,_,(A,B)), body_literal(Rule,Q,_,(A,B)), body_literal(Rule,R,_,(B,C)).
:- prop(not_ab_cb_db,(P,Q,R)), body_literal(Rule,P,_,(A,B)), body_literal(Rule,Q,_,(C,B)), body_literal(Rule,R,_,(D,B)).
:- prop(not_ab_ba_ab,(P,Q,R)), body_literal(Rule,P,_,(A,B)), body_literal(Rule,Q,_,(B,A)), body_literal(Rule,R,_,(A,B)).
:- prop(ab_ba_ab,(P,Q,R)), body_literal(Rule,P,_,(A,B)), body_literal(Rule,Q,_,(B,A)), body_literal(Rule,R,_,(A,B)), valid_var(Rule,A),valid_var(Rule,B).
:- prop(not_ab_ba_bc,(P,Q,R)), body_literal(Rule,P,_,(A,B)), body_literal(Rule,Q,_,(B,A)), body_literal(Rule,R,_,(B,C)).
:- prop(not_ab_cb_dc,(P,Q,R)), body_literal(Rule,P,_,(A,B)), body_literal(Rule,Q,_,(C,B)), body_literal(Rule,R,_,(D,C)).
:- prop(not_ab_ac_db,(P,Q,R)), body_literal(Rule,P,_,(A,B)), body_literal(Rule,Q,_,(A,C)), body_literal(Rule,R,_,(D,B)).
:- prop(not_ab_cb_ad,(P,Q,R)), body_literal(Rule,P,_,(A,B)), body_literal(Rule,Q,_,(C,B)), body_literal(Rule,R,_,(A,D)).
:- prop(not_ab_cb_ba,(P,Q,R)), body_literal(Rule,P,_,(A,B)), body_literal(Rule,Q,_,(C,B)), body_literal(Rule,R,_,(B,A)).
:- prop(ab_cb_ba,(P,Q,R)), body_literal(Rule,P,_,(A,B)), body_literal(Rule,Q,_,(C,B)), body_literal(Rule,R,_,(B,A)), valid_var(Rule,A),valid_var(Rule,B).
:- prop(not_ab_ac_dc,(P,Q,R)), body_literal(Rule,P,_,(A,B)), body_literal(Rule,Q,_,(A,C)), body_literal(Rule,R,_,(D,C)).
:- prop(not_ab_cb_cb,(P,Q,R)), body_literal(Rule,P,_,(A,B)), body_literal(Rule,Q,_,(C,B)), body_literal(Rule,R,_,(C,B)).
:- prop(ab_cb_cb,(P,Q,R)), body_literal(Rule,P,_,(A,B)), body_literal(Rule,Q,_,(C,B)), body_literal(Rule,R,_,(C,B)), valid_var(Rule,C),valid_var(Rule,B).
:- prop(not_ab_ac_ad,(P,Q,R)), body_literal(Rule,P,_,(A,B)), body_literal(Rule,Q,_,(A,C)), body_literal(Rule,R,_,(A,D)).
:- prop(not_ab_cb_cd,(P,Q,R)), body_literal(Rule,P,_,(A,B)), body_literal(Rule,Q,_,(C,B)), body_literal(Rule,R,_,(C,D)).
:- prop(not_ab_ac_cb,(P,Q,R)), body_literal(Rule,P,_,(A,B)), body_literal(Rule,Q,_,(A,C)), body_literal(Rule,R,_,(C,B)).
:- prop(ab_ac_cb,(P,Q,R)), body_literal(Rule,P,_,(A,B)), body_literal(Rule,Q,_,(A,C)), body_literal(Rule,R,_,(C,B)), valid_var(Rule,C),valid_var(Rule,B).
:- prop(not_ab_cb_ca,(P,Q,R)), body_literal(Rule,P,_,(A,B)), body_literal(Rule,Q,_,(C,B)), body_literal(Rule,R,_,(C,A)).
:- prop(ab_cb_ca,(P,Q,R)), body_literal(Rule,P,_,(A,B)), body_literal(Rule,Q,_,(C,B)), body_literal(Rule,R,_,(C,A)), valid_var(Rule,A),valid_var(Rule,C).
:- prop(not_ab_ac_cd,(P,Q,R)), body_literal(Rule,P,_,(A,B)), body_literal(Rule,Q,_,(A,C)), body_literal(Rule,R,_,(C,D)).
:- prop(not_ab_cb_bd,(P,Q,R)), body_literal(Rule,P,_,(A,B)), body_literal(Rule,Q,_,(C,B)), body_literal(Rule,R,_,(B,D)).
:- prop(not_ab_ca_db,(P,Q,R)), body_literal(Rule,P,_,(A,B)), body_literal(Rule,Q,_,(C,A)), body_literal(Rule,R,_,(D,B)).
:- prop(not_ab_bc_db,(P,Q,R)), body_literal(Rule,P,_,(A,B)), body_literal(Rule,Q,_,(B,C)), body_literal(Rule,R,_,(D,B)).
:- prop(not_ab_ac_bd,(P,Q,R)), body_literal(Rule,P,_,(A,B)), body_literal(Rule,Q,_,(A,C)), body_literal(Rule,R,_,(B,D)).
:- prop(not_ab_ca_ad,(P,Q,R)), body_literal(Rule,P,_,(A,B)), body_literal(Rule,Q,_,(C,A)), body_literal(Rule,R,_,(A,D)).
:- prop(not_ab_bc_ad,(P,Q,R)), body_literal(Rule,P,_,(A,B)), body_literal(Rule,Q,_,(B,C)), body_literal(Rule,R,_,(A,D)).
:- prop(not_ab_bc_dc,(P,Q,R)), body_literal(Rule,P,_,(A,B)), body_literal(Rule,Q,_,(B,C)), body_literal(Rule,R,_,(D,C)).
:- prop(not_ab_ca_dc,(P,Q,R)), body_literal(Rule,P,_,(A,B)), body_literal(Rule,Q,_,(C,A)), body_literal(Rule,R,_,(D,C)).
:- prop(not_ab_cb_da,(P,Q,R)), body_literal(Rule,P,_,(A,B)), body_literal(Rule,Q,_,(C,B)), body_literal(Rule,R,_,(D,A)).
:- prop(not_ab_ac_da,(P,Q,R)), body_literal(Rule,P,_,(A,B)), body_literal(Rule,Q,_,(A,C)), body_literal(Rule,R,_,(D,A)).
:- prop(not_ab_bc_cb,(P,Q,R)), body_literal(Rule,P,_,(A,B)), body_literal(Rule,Q,_,(B,C)), body_literal(Rule,R,_,(C,B)).
:- prop(ab_bc_cb,(P,Q,R)), body_literal(Rule,P,_,(A,B)), body_literal(Rule,Q,_,(B,C)), body_literal(Rule,R,_,(C,B)), valid_var(Rule,C),valid_var(Rule,B).
:- prop(not_ab_ca_cd,(P,Q,R)), body_literal(Rule,P,_,(A,B)), body_literal(Rule,Q,_,(C,A)), body_literal(Rule,R,_,(C,D)).

#heuristic size(N). [1000-N,true]

neg_fact(_V0,_V1),acm_id(_V3,_V1),acm_authors(_V3,_V5),sim(_V4,_V5),dblp_authors(_V2,_V4),dblp_id(_V2,_V0)
********** SOLUTION **********
Precision:1.00 Recall:1.00 TP:1 FN:0 TN:2 FP:0 Size:6
eqo(V0,V1):- acm_id(V3,V1),acm_authors(V3,V5),sim(V4,V5),dblp_authors(V2,V4),dblp_id(V2,V0).
******************************
