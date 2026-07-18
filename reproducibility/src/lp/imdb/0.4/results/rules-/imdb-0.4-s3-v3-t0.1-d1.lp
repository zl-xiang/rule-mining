sim(X,X) :- att(T,Attr,X).
sim(X,Y):- sim(Y,X).


eqo(V0,V1):- title_basics(V2),att(V2,tconst,V0),att(V2,primaryTitle,V4),sim(V5,V4),title_basics(V3),att(V3,primaryTitle,V5),att(V3,tconst,V1).
eqo(V0,V1):- title_basics(V2),att(V2,tconst,V0),title_basics(V3),att(V3,tconst,V1),title_akas(V4),att(V4,titleId,V0),att(V4,title,V6),sim(V7,V6),att(V5,title,V7),title_akas(V5),att(V5,titleId,V1).
