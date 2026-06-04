sim(X,X) :- att(T,Attr,X).
sim(X,Y):- sim(Y,X).


eqo(V0,V1):- title_basics(V3),att(V3,tconst,V1),att(V3,primaryTitle,V5),sim(V5,V4),title_basics(V2),att(V2,tconst,V0),att(V2,primaryTitle,V4).
eqo(V0,V1):- title_basics(V2),att(V2,tconst,V0),att(V2,genres,V5),att(V2,titleType,V4),sim(V5,V7),sim(V4,V6),title_basics(V3),att(V3,titleType,V6),att(V3,genres,V7),att(V3,tconst,V1).
