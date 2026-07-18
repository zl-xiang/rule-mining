sim(X,X) :- att(T,Attr,X).
sim(X,Y):- sim(Y,X).


#show.
#show (X,Y): att(V2,id,X),cora(V2), cora(V3), att(V3,id,Y), X!=Y, eqo(X,Y).

eqo(V0,V1):- att(V3,id,V1),cora(V3),att(V3,year,V4),att(V2,year,V4),cora(V2),att(V2,id,V0).
eqo(V0,V1):- att(V3,id,V1),cora(V3),att(V3,publisher,V5),sim(V5,V4),att(V2,publisher,V4),cora(V2),att(V2,id,V0).
eqo(V0,V1):- att(V3,id,V1),cora(V3),att(V3,authors,V5),sim(V4,V5),att(V2,authors,V4),cora(V2),att(V2,id,V0).
eqo(V0,V1):- att(V3,id,V1),cora(V3),att(V3,address,V5),sim(V4,V5),att(V2,id,V0),cora(V2),att(V2,address,V4).
eqo(V0,V1):- att(V3,id,V1),cora(V3),att(V3,journal,V5),sim(V4,V5),att(V2,journal,V4),cora(V2),att(V2,id,V0).
eqo(V0,V1):- att(V3,id,V1),cora(V3),att(V3,title,V5),sim(V5,V4),att(V2,id,V0),cora(V2),att(V2,title,V4).
