sim(X,X) :- att(T,Attr,X).
sim(X,Y):- sim(Y,X).


#show.
#show (X,Y): att(V2,id,X),cora(V2), cora(V3), att(V3,id,Y), X!=Y, eqo(X,Y).

eqo(V0,V1):- att(V2,id,V0),cora(V2),att(V2,editor,V4),att(V2,institution,V5),att(V3,institution,V5),cora(V3),att(V3,id,V1),att(V3,editor,V4).
eqo(V0,V1):- att(V3,id,V1),cora(V3),att(V3,address,V6),att(V3,journal,V7),sim(V4,V6),sim(V5,V7),att(V2,address,V4),cora(V2),att(V2,journal,V5),att(V2,id,V0).
