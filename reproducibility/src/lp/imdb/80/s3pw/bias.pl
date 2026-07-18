% schema info
schema(imdb).

pairwise.

% er_type: 4 - default, 2 - object, 3 - value, 0 - tid
% attributes here should be independent to relations
% title basics
attr(tid,0).
attr(tconst,2).
attr(titleType,4).
attr(primaryTitle,4).
%attr(originalTitle,4).
%attr(isAdult,4).
attr(startYear,4).
attr(genres,4).

% akas
attr(titleId,2).
attr(ordering,4).
attr(region,4).
attr(title,4).

% ratings
attr(averageRating,4).
attr(numVotes,4).

% name basics
%attr(nconst,2).
%attr(primaryName,4).
%attr(primaryProfession,4).

% title_principals
%attr(ordering,4).
%attr(category,4).

compatible_attr(tconst,titleId).

compatible_attr(X,Y) :- compatible_attr(Y,X).
compatible_attr(X,Y) :- compatible_attr(X,Z), compatible_attr(Z,Y).
compatible_attr(X,X) :- attr(X,_), X!=tid.

r(imdb,title_basics,8). 
% r(imdb,name_basics,4).
r(imdb,title_akas,4).
r(imdb,title_ratings,4).
%r(imdb,title_principals, 5).


has_sort(title_basics,tconst).
has_sort(title_basics,titleType).
has_sort(title_basics,primaryTitle).
%has_sort(title_basics,originalTitle).
%has_sort(title_basics,isAdult).
has_sort(title_basics,startYear).
has_sort(title_basics,genres).


%has_sort(name_basics,nconst).
%has_sort(name_basics,primaryName).
%has_sort(name_basics,primaryProfession).


has_sort(title_akas,titleId).
has_sort(title_akas,ordering).
has_sort(title_akas,region).
has_sort(title_akas,title).

has_sort(title_ratings,tconst).
has_sort(title_ratings,averageRating).
has_sort(title_ratings,numVotes).


%has_sort(title_principals,tconst).
%has_sort(title_principals,ordering).
%has_sort(title_principals,category).
%has_sort(title_principals,nconst).

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

target(title_basics,tconst,0).
target(title_basics,tconst,1).

sim_thresh(85).
sim_thresh(90).
sim_thresh(95).

max_body(12).
max_vars(12).

sim_defined(title,title).
sim_defined(titleType,titleType).
sim_defined(genres,genres).
sim_defined(primaryTitle,primaryTitle).