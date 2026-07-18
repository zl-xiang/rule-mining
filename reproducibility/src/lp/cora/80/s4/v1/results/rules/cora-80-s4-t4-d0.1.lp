sim(X,X) :- att(T,Attr,X).
sim(X,Y):- sim(Y,X).


#show.
#show (X,Y): att(V2,id,X),cora(V2), cora(V3), att(V3,id,Y), X!=Y, eqo(X,Y).

eqo(V0,V1):- att(V3,id,V1),cora(V3),att(V3,institution,V5),att(V3,booktitle,V6),sim(V6,V4),att(V2,booktitle,V4),cora(V2),att(V2,id,V0),att(V2,institution,V5).
eqo(V0,V1):- att(V3,id,V1),cora(V3),att(V3,journal,V7),att(V3,publisher,V6),att(V3,editor,V4),sim(V7,V5),att(V2,journal,V5),att(V2,editor,V4),cora(V2),att(V2,publisher,V6),att(V2,id,V0).
