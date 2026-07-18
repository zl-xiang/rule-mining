sim(X,X) :- att(T,Attr,X).
sim(X,Y):- sim(Y,X).


#show.
#show (X,Y): att(V2,id,X),cora(V2), cora(V3), att(V3,id,Y), X!=Y, eqo(X,Y).

eqo(V0,V1):- att(V3,id,V1),cora(V3),att(V3,title,V5),att(V3,pages,V6),sim(V6,V4),att(V2,title,V5),att(V2,pages,V4),att(V2,id,V0),cora(V2).
eqo(V0,V1):- att(V3,id,V1),cora(V3),att(V3,journal,V5),att(V3,pages,V6),sim(V6,V4),att(V2,pages,V4),att(V2,id,V0),cora(V2),att(V2,journal,V5).
eqo(V0,V1):- att(V3,id,V1),cora(V3),att(V3,title,V6),att(V3,institution,V7),sim(V7,V5),sim(V4,V6),att(V2,institution,V5),att(V2,title,V4),att(V2,id,V0),cora(V2).
eqo(V0,V1):- att(V3,id,V1),cora(V3),att(V3,title,V5),att(V3,year,V4),att(V3,authors,V7),sim(V6,V7),att(V2,title,V5),att(V2,year,V4),att(V2,authors,V6),att(V2,id,V0),cora(V2).
