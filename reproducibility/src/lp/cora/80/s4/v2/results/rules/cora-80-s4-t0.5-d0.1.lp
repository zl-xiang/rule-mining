sim(X,X) :- att(T,Attr,X).
sim(X,Y):- sim(Y,X).


#show.
#show (X,Y): att(V2,id,X),cora(V2), cora(V3), att(V3,id,Y), X!=Y, eqo(X,Y).

eqo(V0,V1):- att(V2,id,V0),cora(V2),att(V2,publisher,V6),att(V2,booktitle,V5),att(V2,date,V4),sim(V6,V7),att(V3,publisher,V7),cora(V3),att(V3,id,V1),att(V3,booktitle,V5),att(V3,date,V4).
