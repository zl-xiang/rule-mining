sim(X,X) :- att(T,Attr,X).
sim(X,Y):- sim(Y,X).


#show.
#show (X,Y): att(V2,id,X),cora(V2), cora(V3), att(V3,id,Y), X!=Y, eqo(X,Y).

eqo(V0,V1):- att(V3,id,V1),cora(V3),att(V3,pages,V5),sim(V4,V5),att(V2,pages,V4),cora(V2),att(V2,id,V0).
eqo(V0,V1):- att(V2,id,V0),cora(V2),att(V2,authors,V5),att(V2,title,V4),sim(V5,V6),att(V3,title,V4),cora(V3),att(V3,authors,V6),att(V3,id,V1).
eqo(V0,V1):- att(V2,id,V0),cora(V2),att(V2,title,V5),att(V2,year,V4),sim(V7,V5),sim(V4,V6),att(V3,year,V6),att(V3,title,V7),cora(V3),att(V3,id,V1).
eqo(V0,V1):- att(V2,id,V0),cora(V2),att(V2,title,V4),att(V2,booktitle,V5),sim(V7,V5),sim(V4,V6),att(V3,title,V6),cora(V3),att(V3,booktitle,V7),att(V3,id,V1).
