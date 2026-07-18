sim(X,X):- att(T,A,X).
              sim(Y,X):- sim(X,Y).

eqo(V0,V1):- title_basics(V3),att(V3,tconst,V1),att(V3,primaryTitle,V4),title_basics(V2),att(V2,tconst,V0),att(V2,primaryTitle,V4).
eqo(V0,V1):- title_basics(V2),att(V2,tconst,V0),att(V2,primaryTitle,V5),att(V2,startYear,V6),att(V2,genres,V4),sim(V5,V7),title_basics(V3),att(V3,primaryTitle,V7),att(V3,tconst,V1),att(V3,startYear,V6),att(V3,genres,V4).
