% schema info
schema(cddb).

% er_type: 4 - default, 2 - object, 3 - value, 0 - tid
% attributes here should be independent to relations
attr(tid,0).
attr(artist,3).
attr(category,3).
attr(genre,3).
attr(id,2).
attr(title,3).
% attr(tracks,3).
attr(year,3).


compatible_attr(X,Y) :- compatible_attr(Y,X).
compatible_attr(X,Y) :- compatible_attr(X,Z), compatible_attr(Z,Y).
compatible_attr(X,X) :- attr(X,_).

r(cddb,cddb,8).


has_sort(cddb,artist).
has_sort(cddb,category).
has_sort(cddb,genre).
has_sort(cddb,id).
has_sort(cddb,title).
% has_sort(cddb,tracks).
has_sort(cddb,year).




% language constructs
head_pred(eqo,2).

body_pred(cddb,1).
body_pred(sim,2).
body_pred(att,3).



head_pred(eqo,2).

body_pred(sim,2).
body_pred(att,3).
% body_pred(range,2).

body_pred(R,1):- r(S,R,A). 
const(att,2).


{type(eqo,(Aname1,Aname2));type(sim,(Aname1,Aname2))}=2 :- compatible_attr(Aname1,Aname2).


type(R,(tid)) :- r(_,R,_). 

% shall tid be a unified attribute?
type(att,(tid,attr,Aname)):- attr(Aname,_), Aname!= tid.
% type(range,(tid,relation)).


target(cddb,id,0).
target(cddb,id,1).
max_body(10).
max_vars(8).


pairwise.