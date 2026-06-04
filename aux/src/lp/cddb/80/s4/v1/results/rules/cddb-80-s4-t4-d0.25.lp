sim(X,X) :- att(T,Attr,X).
sim(X,Y):- sim(Y,X).


#show.
#show (X,Y): att(V2,id,X),cddb(V2), cddb(V3), att(V3,id,Y), X!=Y, eqo(X,Y).

eqo(V0,V1):- att(V2,id,V0),cddb(V2),att(V2,artist,V4),sim(V5,V4),att(V3,artist,V5),cddb(V3),att(V3,id,V1).
eqo(V0,V1):- att(V2,id,V0),cddb(V2),att(V2,title,V4),sim(V5,V4),att(V3,title,V5),cddb(V3),att(V3,id,V1).
eqo(V0,V1):- att(V3,id,V1),cddb(V3),att(V3,genre,V5),sim(V5,V4),att(V2,id,V0),cddb(V2),att(V2,genre,V4).
