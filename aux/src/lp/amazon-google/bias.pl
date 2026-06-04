% schema info
schema(amazon_google).

% er_type: 4 - default, 2 - object, 3 - value, 0 - tid
% attributes here should be independent to relations
attr(tid,0).
attr(aid,2).
attr(atitle,4).
attr(adescription,4).
attr(amanufacturer,4).
attr(aprice,4).

attr(gid,2).
attr(gtitle,4).
attr(gdescription,4).
attr(gmanufacturer,4).
attr(gprice,4).


compatible_attr(aid,gid).
compatible_attr(atitle,gtitle).
compatible_attr(adescription,gdescription).
compatible_attr(amanufacturer,gmanufacturer).
compatible_attr(aprice,gprice).
compatible_attr(X,Y) :- compatible_attr(Y,X).
compatible_attr(X,Y) :- compatible_attr(X,Z), compatible_attr(Z,Y).
compatible_attr(X,X) :- compatible_attr(X,_).

r(amazon_google,amazon,6).
r(amazon_google,google,6).


has_sort(amazon,aid).
has_sort(amazon,atitle).
has_sort(amazon,adescription).
has_sort(amazon,amanufacturer).
has_sort(amazon,aprice).  



has_sort(google,gid).
has_sort(google,gtitle).
has_sort(google,gdescription).
has_sort(google,gmanufacturer).
has_sort(google,gprice).



% language constructs
head_pred(eqo,2).

body_pred(amazon,1).
body_pred(google,1).
body_pred(sim,2).
body_pred(att,3).
body_pred(range,2).

const(att,2).
{type(eqo,(Aname1,Aname2));type(sim,(Aname1,Aname2))}=2 :- compatible_attr(Aname1,Aname2).


% shall tid be a unified attribute?
type(att,(tid,attr,Aname)):- attr(Aname,_), Aname!= tid.
type(range,(tid,relation)).
type(amazon,(tid)).
type(google,(tid)).

target(amazon,aid,0).
target(google,gid,1).
max_body(10).
max_vars(8).

pairwise.
