eqo(V0,V1):- title_basics(V2),att(V2,tconst,V0),att(V2,primaryTitle,V4),title_basics(V3),att(V3,primaryTitle,V4),att(V3,tconst,V1).
eqo(V0,V1):- title_basics(V3),att(V3,tconst,V1),att(V3,genres,V5),att(V3,primaryTitle,V6),sim(V4,V6),title_basics(V2),att(V2,genres,V5),att(V2,primaryTitle,V4),att(V2,tconst,V0).
eqo(V0,V1):- title_basics(V3),att(V3,tconst,V1),title_basics(V2),att(V2,tconst,V0),title_akas(V5),att(V5,titleId,V1),att(V5,title,V6),att(V4,title,V6),att(V4,titleId,V0),title_akas(V4).
eqo(V0,V1):- title_ratings(V4),att(V4,tconst,V0),att(V4,averageRating,V8),title_basics(V3),att(V3,tconst,V1),att(V3,primaryTitle,V7),sim(V6,V7),title_basics(V2),att(V2,tconst,V0),att(V2,primaryTitle,V6),title_ratings(V5),att(V5,averageRating,V8),att(V5,tconst,V1).
