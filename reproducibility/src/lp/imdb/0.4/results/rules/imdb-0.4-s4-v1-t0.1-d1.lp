eqo(V0,V1):- title_basics(V3),att(V3,tconst,V1),title_basics(V2),att(V2,tconst,V0),title_akas(V5),att(V5,titleId,V0),att(V5,title,V6),att(V4,title,V6),title_akas(V4),att(V4,titleId,V1).
eqo(V0,V1):- title_basics(V3),att(V3,tconst,V1),att(V3,titleType,V7),att(V3,primaryTitle,V6),sim(V4,V6),sim(V7,V5),title_basics(V2),att(V2,primaryTitle,V4),att(V2,tconst,V0),att(V2,titleType,V5).
