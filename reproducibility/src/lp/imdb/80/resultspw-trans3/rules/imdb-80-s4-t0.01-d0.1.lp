sim(X,X):- att(T,A,X).
              sim(Y,X):- sim(X,Y).

eqo(V0,V1):- title_basics(V3),att(V3,tconst,V1),att(V3,primaryTitle,V4),title_basics(V2),att(V2,primaryTitle,V4),att(V2,tconst,V0).
eqo(V0,V1):- title_basics(V2),att(V2,tconst,V0),att(V2,startYear,V6),att(V2,titleType,V5),att(V2,primaryTitle,V4),sim(V5,V7),sim(V4,V8),title_basics(V3),att(V3,titleType,V7),att(V3,tconst,V1),att(V3,primaryTitle,V8),att(V3,startYear,V6).
