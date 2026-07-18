sim(X,X) :- att(T,Attr,X).
sim(X,Y):- sim(Y,X).
:-cora(T1),cora(T2),att(T1,id,X),att(T2,id,Y),eqo(X,Y),att(T1,title,S1),att(T2,title,S2),not sim(S1,S2).

#show.
#show (X,Y): att(V2,id,X),cora(V2), cora(V3), att(V3,id,Y), X!=Y, eqo(X,Y).


sim(X,X) :- att(T,Attr,X).
sim(X,Y):- sim(Y,X).


#show.
#show (X,Y): att(V2,id,X),cora(V2), cora(V3), att(V3,id,Y), X!=Y, eqo(X,Y).

activeo(V0,V1) :- att(V3,id,V1),cora(V3),att(V3,publisher,V5),att(V2,id,V0),cora(V2),att(V2,publisher,V4),sim(V5,V4).
activeo(V0,V1) :- att(V3,id,V1),cora(V3),att(V3,authors,V5),att(V2,id,V0),cora(V2),att(V2,authors,V4),sim(V5,V4).
activeo(V0,V1) :- att(V3,id,V1),cora(V3),att(V3,year,V5),att(V2,id,V0),cora(V2),att(V2,year,V4),sim(V5,V4).
