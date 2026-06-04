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


has_sort(dblp,did).
has_sort(dblp,dtitle).
has_sort(dblp,dauthors).
has_sort(dblp,dvenue).
has_sort(dblp,dyear).  


has_sort(acm,aid).
has_sort(acm,atitle).
has_sort(acm,aauthors).
has_sort(acm,avenue).
has_sort(acm,ayear).



% language bias
head_pred(eqo,2).

% body_pred(dblp,1).
% body_pred(acm,1).
body_pred(sim,2).
body_pred(att,3).
body_pred(range,2).

const(att,2).

% body_pred(R,2) :- r(_,R,_).

% type(eqo,(did,aid)).
% type(eqo,(aid,did)).
% type(sim,(dtitle,atitle)).

{type(eqo,(Aname1,Aname2));type(sim,(Aname1,Aname2))}=2 :- compatible_attr(Aname1,Aname2).


% shall tid be a unified attribute?
type(att,(tid,attr,Aname)):- attr(Aname,_), Aname!= tid.
type(range,(tid,relation)).

target(dblp,did,0).
target(acm,aid,1).
max_body(10).
max_vars(6).


