%% ##################################################
%% THIS FILE CONTAINS THE ASP PROGRAM GENERATOR, CALLED ALAN
%% ##################################################

#defined direction_/3.
#defined type/2.
#defined non_datalog/0.
#show body_literal/4.
#show connected/3.
% #show var_member/2.
%#show head_var/2.
#show fixed_var_type/2.
% #show pred_arg_type/3.
% #show(var_pos,Var, Vars, Pos):pred_arg_type(P, Pos, Type), var_pos(Var, Vars, Pos).
% #show bad_body/2.

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
% :- not size(_).

%% ********** BASE CASE (RULE 0) **********
head_literal(0,eqo,A,Vars):-
    head_pred(eqo,A),
    head_vars(A,Vars). % only one head_vars-fact head_vars(eqo,(0,1)).

% to generate only those relevant to head
%% Picking body literals
% Base case, always starts with the relations that bound the head variables
{body_literal(0,att,3,Vars):var_pos(Var,Vars,2),
    const_pos(Attr,Vars,1),
    type_pos(Types, 2, Attr),
    type(att,Types),
    fixed_var_type(Var,Attr)}=2.

% Generate whatever
% Similarity joins
{body_literal(0,sim,2,Vars)}:-
    var_pos(Svar1, Vars, 0),
    var_pos(Svar2, Vars, 1),
    body_literal(0,att,3,Bvars1),
    body_literal(0,att,3,Bvars2),
    const_pos(Attr1, Bvars1, 1), 
    const_pos(Attr2, Bvars, 1),
    compatible_attr(Attr1,Attr2),
    var_pos(Svar1, Bvars1, 2),
    var_pos(Svar2, Bvars2, 2), Svar1 != Svar2.

% Joins
% same tuple but different attributes
{body_literal(0,att,3,Bvars)}:-
    body_literal(0,att,3,Bvars1),
    const_pos(Attr1, Bvars1, 1), const_pos(Attr2, Bvars, 1),
    var_pos(Tid1, Bvars1, 0), var_pos(Tid2, Bvars, 0), compatible_attr(Attr1,Attr2), Attr1!=Attr2,
    var_pos(Var, Bvars, 2), var_pos(Var, Bvars1, 2).

{body_literal(0,att,3,Bvars)}:-
    body_literal(0,att,3,Bvars1),
    const_pos(Attr1, Bvars1, 1), const_pos(Attr2, Bvars, 1),
    var_pos(Tid1, Bvars1, 0), var_pos(Tid2, Bvars, 0), Tid1!= Tid2, compatible_attr(Attr1,Attr2),
    var_pos(Var, Bvars, 2), var_pos(Var, Bvars1, 2).

% % different tuples
% {body_literal(0,att,3,Bvars)}:-
%     body_literal(0,att,3,Bvars1),const_pos(Attr, Bvars1, 1), const_pos(Attr, Bvars, 1),
%     compatible_attr(Attr1,Attr2),
%     var_pos(Tid, Bvars1, 0), var_pos(Tid1, Bvars, 0),Tid1!=Tid,
%     var_pos(Var, Bvars, 2), var_pos(Var, Bvars1, 2).

% body_literal(0,att,3,(0,dtitle,2)).
% body_literal(0,att,3,(1,atitle,3)).
% body_literal(0,sim,2,(2,3)).

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
%% Leon: at the moment no constants occur in head, but may need to change later
clause_var(C,Var):-
    head_var(C,Var).

clause_var(C,Var):-
    body_var(C,Var).

%% HEAD VAR
head_var(C,Var):-
    head_literal(C,_,_,Vars), % (0,1)
    var_member(Var,Vars).

%% BODY VAR
body_var(C,Var):-
    body_literal(C,P,A,Vars),
    % var_member(Var,Vars), 
    var_pos(Var,Vars,Pos), not const(P,Pos).

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


%% MUST BE CONNECTED
%%%%%%%%%% Leon ER rule connectivity %%%%%%%%%%%%
% A tuple variable Tid is connected if it occurs in head
% The rule says a tuple variable Tid is connected in rule R
% if for a variable Var occurs in head of some object rule,
% and Var also occurs the in associated attribute body literal of Tid in the rule R

% Similarity join
connected(R,Tid,Tid1):-
    body_literal(R,att,_,Bvars),
    var_pos(Tid, Bvars, 0), 
    var_pos(Var, Bvars, 2),
    body_literal(R,att,_,Bvars1),
    var_pos(Tid1, Bvars1, 0), var_pos(Var1, Bvars1, 2),
    body_literal(R,sim,_,Svars), var_member(Var,Svars), var_member(Var1,Svars).


% Equality join
connected(R,Tid,Tid1):-
    body_literal(R,att,_,Bvars), var_pos(Var, Bvars, 2),
    var_pos(Tid, Bvars, 0),
    body_literal(R,att,_,Bvars1), var_pos(Tid1, Bvars1, 0), var_pos(Var, Bvars1, 2).

connected(R,Tid,Tid1) :- connected(R,Tid,Tid2), connected(R,Tid2,Tid1).


%% TODO: check why the following do not generate connected rule
% connected(0,0,0) body_literal(0,att,3,(0,dtitle,2)) body_literal(0,att,3,(1,atitle,3)) 
% body_literal(0,sim,2,(2,3)) body_literal(0,att,3,(0,did,1)) body_literal(0,att,3,(1,aid,0)) 
% fixed_var_type(1,did,dblp) fixed_var_type(0,aid,acm)
:- not connected(R,Tid, Tid1), body_literal(R,att,_,Bvars),
    var_pos(Tid, Bvars, 0), body_literal(R,att,_,Bvars1),var_pos(Tid1, Bvars1, 0) .

%%%%%%%%%% ER rule mining connectivity %%%%%%%%%%%%

% head_connected(C,Var):-
%     head_var(C,Var).
% head_connected(C,Var1):-
%     head_literal(C,_,A,_),
%     Var1 >= A,
%     head_connected(C,Var2),
%     body_literal(C,_,_,Vars),
%     var_member(Var1,Vars),
%     var_member(Var2,Vars),
%     Var1 != Var2.

%% violated %%
% :-
%     head_literal(C,_,A,_),
%     Var >= A,
%     body_var(C,Var),
%     not head_connected(C,Var).
% any two body literals generated with the same tuple id variable cannot have a pair of attributes that do not co-occur in any relation
:- body_literal(C,att,3,Vars1), body_literal(C,att,3,Vars2),  
        var_pos(Tid,Vars1,0),  var_pos(Tid,Vars2,0), const_pos(Attr1,Vars1,1), const_pos(Attr2,Vars2,1), #count{R:has_sort(R,Attr1),has_sort(R,Attr2)}<1.

% % any two body literals with the same tuple id var and the same attribute cannot bind to different variables
:- body_literal(C,att,3,Vars1), body_literal(C,att,3,Vars2),  
        var_pos(Tid,Vars1,0),  var_pos(Tid,Vars2,0), const_pos(Attr,Vars1,1), const_pos(Attr,Vars2,1), Vars1!=Vars2.

% any sim-atom in rule bodies need to be on attributes thats are compatible

% any join in rule bodies need to be on attributes thats are compatible
        
% fixing type of variable Var to Type when it occurs on head
% {fixed_var_type(Var, Type, R): type(eqo, Types),
% type_pos(Types, Pos, Type), target(R,Type), var_pos(Var, Vars, Pos)}=2 :- head_literal(_, eqo, _, Vars).
fixed_var_type(Var, Type) :- type(eqo, Types),
        type_pos(Types, Pos, Type), target(R,Type,Pos), var_pos(Var, Vars, Pos), head_literal(_, eqo, _, Vars).

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



% :-
%     direction_(_,_,_),
%     body_var(Rule,Var),
%     not safe_bvar(Rule,Var).

% :- appears((V0,V1,V2)), gap((V0,V1,V2), V), not seen_lower((V0,V1,V2),V), not head_var(_,V).


#heuristic size(N). [1000-N,true]

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

%has_sort(dblp,tid).
has_sort(dblp,did).
has_sort(dblp,dtitle).
has_sort(dblp,dauthors).
has_sort(dblp,dvenue).
has_sort(dblp,dyear).  


%has_sort(acm,tid).
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

target(dblp,did,0).
target(acm,aid,1).





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
%% added to test sim connectivity
vars(2, (2, 3)).
var_pos(2, (2, 3), 0).
var_pos(3, (2, 3), 1).
vars(3, (1, atitle, 3)).

var_pos(1, (1, atitle, 3), 0).
var_pos(3, (1, atitle, 3), 2).

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