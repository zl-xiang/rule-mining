sim(X,X) :- att(T,Attr,X).
sim(X,Y):- sim(Y,X).


#show.
#show (X,Y): att(V2,id,X),cora(V2), cora(V3), att(V3,id,Y), X!=Y, eqo(X,Y).

eqo(V0,V1):- att(V2,id,V0),cora(V2),att(V2,authors,V4),att(V2,title,V5),sim(V4,V6),att(V3,id,V1),att(V3,authors,V6),att(V3,title,V5),cora(V3).
eqo(V0,V1):- att(V2,id,V0),cora(V2),att(V2,title,V5),att(V2,year,V4),sim(V4,V6),sim(V7,V5),att(V3,id,V1),att(V3,year,V6),att(V3,title,V7),cora(V3).
eqo(V0,V1):- att(V2,id,V0),cora(V2),att(V2,title,V5),att(V2,address,V4),sim(V4,V6),sim(V7,V5),att(V3,address,V6),att(V3,id,V1),att(V3,title,V7),cora(V3).
eqo(V0,V1):- att(V2,id,V0),cora(V2),att(V2,title,V5),att(V2,booktitle,V4),sim(V4,V6),sim(V7,V5),att(V3,id,V1),att(V3,booktitle,V6),att(V3,title,V7),cora(V3).
