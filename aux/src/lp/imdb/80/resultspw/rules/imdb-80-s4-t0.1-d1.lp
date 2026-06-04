sim(X,X):- att(T,A,X).
              sim(Y,X):- sim(X,Y).

eqo(V0,V1):- title_basics(V3),att(V3,tconst,V1),att(V3,primaryTitle,V4),title_basics(V2),att(V2,primaryTitle,V4),att(V2,tconst,V0).
eqo(V0,V1):- title_basics(V3),att(V3,tconst,V1),att(V3,startYear,V5),att(V3,primaryTitle,V6),sim(V6,V4),title_basics(V2),att(V2,tconst,V0),att(V2,startYear,V5),att(V2,primaryTitle,V4).
eqo(V0,V1):- title_basics(V3),att(V3,tconst,V1),att(V3,primaryTitle,V7),att(V3,genres,V9),att(V3,titleType,V8),sim(V7,V4),sim(V6,V9),sim(V5,V8),title_basics(V2),att(V2,genres,V6),att(V2,tconst,V0),att(V2,primaryTitle,V4),att(V2,titleType,V5).
