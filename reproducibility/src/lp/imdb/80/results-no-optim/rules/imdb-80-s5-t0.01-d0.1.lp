sim(X,X):- att(T,A,X).
              sim(Y,X):- sim(X,Y).

eqo(V0,V1):- title_basics(V3),att(V3,tconst,V1),att(V3,primaryTitle,V4),title_basics(V2),att(V2,tconst,V0),att(V2,primaryTitle,V4).
eqo(V0,V1):- title_basics(V2),att(V2,tconst,V0),title_basics(V3),att(V3,tconst,V1),title_akas(V4),att(V4,titleId,V1),att(V4,region,V7),att(V4,title,V6),att(V5,title,V6),title_akas(V5),att(V5,titleId,V0),att(V5,region,V7).
eqo(V0,V1):- title_basics(V2),att(V2,tconst,V0),att(V2,genres,V6),title_basics(V3),att(V3,tconst,V1),att(V3,genres,V6),title_akas(V4),att(V4,titleId,V1),att(V4,title,V7),att(V5,titleId,V0),title_akas(V5),att(V5,title,V7).
eqo(V0,V1):- title_basics(V2),att(V2,tconst,V0),att(V2,titleType,V6),title_basics(V3),att(V3,titleType,V6),att(V3,tconst,V1),title_akas(V4),att(V4,titleId,V1),att(V4,title,V7),att(V5,title,V7),title_akas(V5),att(V5,titleId,V0).
