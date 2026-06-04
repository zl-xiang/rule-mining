sim(X,X):- att(T,A,X).
              sim(Y,X):- sim(X,Y).

eqo(V0,V1):- title_basics(V2),att(V2,tconst,V0),att(V2,primaryTitle,V4),title_basics(V3),att(V3,tconst,V1),att(V3,primaryTitle,V4).
eqo(V0,V1):- title_basics(V3),att(V3,tconst,V1),att(V3,startYear,V6),att(V3,primaryTitle,V7),att(V3,genres,V5),sim(V4,V7),title_basics(V2),att(V2,primaryTitle,V4),att(V2,tconst,V0),att(V2,genres,V5),att(V2,startYear,V6).
eqo(V0,V1):- title_ratings(V5),att(V5,tconst,V0),att(V5,numVotes,V8),title_ratings(V4),att(V4,tconst,V1),att(V4,numVotes,V8),title_basics(V3),att(V3,tconst,V1),att(V3,primaryTitle,V7),sim(V6,V7),title_basics(V2),att(V2,primaryTitle,V6),att(V2,tconst,V0).
eqo(V0,V1):- title_basics(V3),att(V3,tconst,V1),att(V3,titleType,V7),sim(V7,V6),title_basics(V2),att(V2,titleType,V6),att(V2,tconst,V0),title_akas(V5),att(V5,titleId,V0),att(V5,title,V8),att(V4,titleId,V1),att(V4,title,V8),title_akas(V4).
