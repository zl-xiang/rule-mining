eqo(V0,V1):- title_basics(V3),att(V3,tconst,V1),att(V3,primaryTitle,V5),sim(V5,V4),title_basics(V2),att(V2,tconst,V0),att(V2,primaryTitle,V4).
eqo(V0,V1):- title_ratings(V5),att(V5,tconst,V0),att(V5,numVotes,V7),title_basics(V2),att(V2,tconst,V0),att(V2,startYear,V6),title_basics(V3),att(V3,tconst,V1),att(V3,startYear,V6),title_ratings(V4),att(V4,tconst,V1),att(V4,numVotes,V7).
