sim(X,X) :- att(T,Attr,X).
sim(X,Y):- sim(Y,X).


eqo(V0,V1):- title_basics(V3),att(V3,tconst,V1),att(V3,primaryTitle,V4),title_basics(V2),att(V2,tconst,V0),att(V2,primaryTitle,V4).
eqo(V0,V1):- title_basics(V2),att(V2,tconst,V0),title_basics(V3),att(V3,tconst,V1),title_akas(V4),att(V4,titleId,V1),att(V4,title,V6),att(V5,title,V6),att(V5,titleId,V0),title_akas(V5).
eqo(V0,V1):- title_basics(V2),att(V2,tconst,V0),att(V2,genres,V5),att(V2,startYear,V7),att(V2,primaryTitle,V6),att(V2,titleType,V4),sim(V10,V4),sim(V9,V5),sim(V6,V8),title_basics(V3),att(V3,tconst,V1),att(V3,titleType,V10),att(V3,startYear,V7),att(V3,genres,V9),att(V3,primaryTitle,V8).
