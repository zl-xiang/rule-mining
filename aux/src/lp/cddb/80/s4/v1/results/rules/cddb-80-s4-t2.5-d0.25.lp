sim(X,X) :- att(T,Attr,X).
sim(X,Y):- sim(Y,X).


#show.
#show (X,Y): att(V2,id,X),cddb(V2), cddb(V3), att(V3,id,Y), X!=Y, eqo(X,Y).

eqo(V0,V1):- att(V3,id,V1),cddb(V3),att(V3,artist,V4),att(V2,artist,V4),cddb(V2),att(V2,id,V0).
eqo(V0,V1):- att(V3,id,V1),cddb(V3),att(V3,title,V5),sim(V5,V4),att(V2,title,V4),cddb(V2),att(V2,id,V0).
eqo(V0,V1):- att(V3,id,V1),cddb(V3),att(V3,year,V7),att(V3,genre,V6),sim(V5,V7),sim(V4,V6),att(V2,year,V5),att(V2,genre,V4),cddb(V2),att(V2,id,V0).
eqo(V0,V1):- att(V3,id,V1),cddb(V3),att(V3,category,V6),att(V3,artist,V7),sim(V5,V6),sim(V4,V7),att(V2,category,V5),att(V2,artist,V4),cddb(V2),att(V2,id,V0).
