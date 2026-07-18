sim(X,X):- att(T,A,X).
              sim(Y,X):- sim(X,Y).

eqo(V0,V1):- title_basics(V2),att(V2,tconst,V0),att(V2,primaryTitle,V4),title_basics(V3),att(V3,tconst,V1),att(V3,primaryTitle,V4).
eqo(V0,V1):- title_basics(V3),att(V3,tconst,V1),att(V3,startYear,V5),att(V3,titleType,V7),att(V3,primaryTitle,V8),sim(V4,V8),sim(V7,V6),title_basics(V2),att(V2,primaryTitle,V4),att(V2,startYear,V5),att(V2,tconst,V0),att(V2,titleType,V6).
