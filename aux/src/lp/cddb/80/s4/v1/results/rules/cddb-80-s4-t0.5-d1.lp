sim(X,X) :- att(T,Attr,X).
sim(X,Y):- sim(Y,X).


#show.
#show (X,Y): att(V2,id,X),cddb(V2), cddb(V3), att(V3,id,Y), X!=Y, eqo(X,Y).

eqo(V0,V1):- att(V2,id,V0),cddb(V2),att(V2,year,V4),att(V2,artist,V5),att(V3,year,V4),cddb(V3),att(V3,id,V1),att(V3,artist,V5).
eqo(V0,V1):- att(V2,id,V0),cddb(V2),att(V2,title,V4),att(V2,year,V5),sim(V7,V4),sim(V5,V6),att(V3,year,V6),cddb(V3),att(V3,id,V1),att(V3,title,V7).
eqo(V0,V1):- att(V2,id,V0),cddb(V2),att(V2,title,V4),att(V2,artist,V5),sim(V7,V4),sim(V5,V6),att(V3,artist,V6),cddb(V3),att(V3,id,V1),att(V3,title,V7).
eqo(V0,V1):- att(V2,id,V0),cddb(V2),att(V2,genre,V4),att(V2,year,V5),sim(V4,V7),sim(V5,V6),att(V3,year,V6),cddb(V3),att(V3,id,V1),att(V3,genre,V7).
eqo(V0,V1):- att(V2,id,V0),cddb(V2),att(V2,artist,V5),att(V2,genre,V4),sim(V4,V7),sim(V6,V5),att(V3,artist,V6),cddb(V3),att(V3,id,V1),att(V3,genre,V7).
