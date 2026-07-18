sim(X,X) :- att(T,Attr,X).
sim(X,Y):- sim(Y,X).


eqo(V0,V1):- title_basics(V2),att(V2,tconst,V0),att(V2,titleType,V4),att(V2,primaryTitle,V5),sim(V7,V4),sim(V6,V5),title_basics(V3),att(V3,tconst,V1),att(V3,primaryTitle,V6),att(V3,titleType,V7).
