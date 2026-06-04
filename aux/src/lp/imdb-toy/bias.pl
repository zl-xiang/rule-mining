% schema info
schema(imdb).

% er_type: 4 - default, 2 - object, 3 - value, 0 - tid
% attributes here should be independent to relations
attr(tid,0).
attr(mid,2).
attr(title,4).
attr(cid,2).
attr(rid,2).
attr(name,4).
attr(gender,4).
attr(score,4).
attr(website,4).


compatible_attr(X,Y) :- compatible_attr(Y,X).
compatible_attr(X,Y) :- compatible_attr(X,Z), compatible_attr(Z,Y).
compatible_attr(X,X) :- attr(X,_), X!=tid.

r(imdb,movie,5). % mid, title, cid, rid
r(imdb,cast,4). % cid, name, gender
r(imdb,review,4). % rid, score, website


has_sort(movie,mid).
has_sort(movie,title).
has_sort(movie,cid).
has_sort(movie,rid).

has_sort(cast,cid).
has_sort(cast,name).
has_sort(cast,gender).

has_sort(review,rid).
has_sort(review,score).
has_sort(review,website).  


% language constructs
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

target(movie,mid,0).
target(movie,mid,1).
max_body(15).
max_vars(12).



