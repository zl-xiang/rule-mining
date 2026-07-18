% schema info
schema(dblp_scholar).

% er_type: 4 - default, 2 - object, 3 - value, 0 - tid
% attributes here should be independent to relations
attr(tid,0).
attr(did,2).
attr(dtitle,4).
attr(dauthors,4).
attr(dvenue,4).
attr(dyear,4).

% attr(a_tid,0).
attr(sid,2).
attr(stitle,4).
attr(sauthors,4).
attr(svenue,4).
attr(syear,4).


compatible_attr(did,sid).
compatible_attr(dtitle,stitle).
compatible_attr(dauthors,sauthors).
compatible_attr(dvenue,svenue).
compatible_attr(dyear,syear).
compatible_attr(X,Y) :- compatible_attr(Y,X).
compatible_attr(X,Y) :- compatible_attr(X,Z), compatible_attr(Z,Y).
compatible_attr(X,X) :- compatible_attr(X,_).

r(dblp_scholar,dblp,6).
r(dblp_scholar,scholar,6).


has_sort(dblp,did).
has_sort(dblp,dtitle).
has_sort(dblp,dauthors).
has_sort(dblp,dvenue).
has_sort(dblp,dyear).  



has_sort(scholar,sid).
has_sort(scholar,stitle).
has_sort(scholar,sauthors).
has_sort(scholar,svenue).
has_sort(scholar,syear).



% language constructs
head_pred(eqo,2).

body_pred(dblp,1).
body_pred(scholar,1).
body_pred(sim,2).
body_pred(att,3).
body_pred(range,2).

const(att,2).
{type(eqo,(Aname1,Aname2));type(sim,(Aname1,Aname2))}=2 :- compatible_attr(Aname1,Aname2).


% shall tid be a unified attribute?
type(att,(tid,attr,Aname)):- attr(Aname,_), Aname!= tid.
type(range,(tid,relation)).
type(dblp,(tid)).
type(scholar,(tid)).

target(dblp,did,0).
target(scholar,sid,1).
max_body(10).
max_vars(8).

pairwise.
