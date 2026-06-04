sim(X,X) :- att(T,Attr,X).
sim(X,Y):- sim(Y,X).


#show.
#show (X,Y): att(V2,id,X),cora(V2), cora(V3), att(V3,id,Y), X!=Y, eqo(X,Y).

eqo(V0,V1):- att(V2,id,V0),cora(V2),att(V2,title,V4),att(V3,id,V1),cora(V3),att(V3,title,V4).
eqo(V0,V1):- att(V2,id,V0),cora(V2),att(V2,pages,V4),sim(V5,V4),att(V3,pages,V5),cora(V3),att(V3,id,V1).
eqo(V0,V1):- att(V2,id,V0),cora(V2),att(V2,date,V4),sim(V5,V4),att(V3,id,V1),cora(V3),att(V3,date,V5).
eqo(V0,V1):- att(V2,id,V0),cora(V2),att(V2,editor,V4),sim(V5,V4),att(V3,id,V1),cora(V3),att(V3,editor,V5).
eqo(V0,V1):- att(V3,id,V1),cora(V3),att(V3,year,V7),att(V3,title,V6),sim(V4,V7),sim(V6,V5),att(V2,title,V5),att(V2,id,V0),cora(V2),att(V2,year,V4).
eqo(V0,V1):- att(V3,id,V1),cora(V3),att(V3,address,V6),att(V3,title,V7),sim(V4,V7),sim(V6,V5),att(V2,title,V4),att(V2,address,V5),att(V2,id,V0),cora(V2).
