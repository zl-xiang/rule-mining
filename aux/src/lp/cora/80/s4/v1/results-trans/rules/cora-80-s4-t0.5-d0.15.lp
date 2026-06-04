sim(X,X) :- att(T,Attr,X).
sim(X,Y):- sim(Y,X).


#show.
#show (X,Y): att(V2,id,X),cora(V2), cora(V3), att(V3,id,Y), X!=Y, eqo(X,Y).

eqo(V0,V1):- att(V3,id,V1),cora(V3),att(V3,booktitle,V6),att(V3,date,V4),sim(V5,V6),att(V2,booktitle,V5),cora(V2),att(V2,date,V4),att(V2,id,V0).
eqo(V0,V1):- att(V3,id,V1),cora(V3),att(V3,institution,V4),att(V3,title,V6),sim(V5,V6),att(V2,institution,V4),cora(V2),att(V2,id,V0),att(V2,title,V5).
