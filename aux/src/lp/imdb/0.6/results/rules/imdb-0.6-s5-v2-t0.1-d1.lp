sim(X,X) :- att(T,Attr,X).
sim(X,Y):- sim(Y,X).
eqo(X,X):-att(T,tconst,X).
eqo(X,X):-att(T,titleId,X).

eqo(V0,V1):- title_basics(V3),att(V3,tconst,V1),att(V3,primaryTitle,V6),att(V3,titleType,V7),sim(V6,V5),sim(V7,V4),title_basics(V2),att(V2,titleType,V4),att(V2,tconst,V0),att(V2,primaryTitle,V5).
eqo(V0,V1):- title_basics(V3),att(V3,tconst,V1),title_basics(V2),att(V2,tconst,V0),title_akas(V5),att(V5,titleId,V1),att(V5,title,V6),att(V4,title,V6),att(V4,titleId,V0),title_akas(V4).
