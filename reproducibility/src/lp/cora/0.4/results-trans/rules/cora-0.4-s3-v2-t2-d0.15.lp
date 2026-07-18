sim(X,X) :- att(T,Attr,X).
sim(X,Y):- sim(Y,X).


#show.
#show (X,Y): att(V2,id,X),cora(V2), cora(V3), att(V3,id,Y), X!=Y, eqo(X,Y).

eqo(V0,V1):- att(V3,id,V1),cora(V3),att(V3,title,V4),att(V2,title,V4),att(V2,id,V0),cora(V2).
eqo(V0,V1):- att(V3,id,V1),cora(V3),att(V3,booktitle,V5),sim(V5,V4),att(V2,booktitle,V4),att(V2,id,V0),cora(V2).
eqo(V0,V1):- att(V3,id,V1),cora(V3),att(V3,title,V7),att(V3,authors,V6),sim(V6,V5),sim(V4,V7),att(V2,id,V0),cora(V2),att(V2,authors,V5),att(V2,title,V4).
