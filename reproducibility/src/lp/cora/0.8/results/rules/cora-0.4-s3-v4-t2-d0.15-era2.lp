sim(X,X) :- att(T,Attr,X).
sim(X,Y):- sim(Y,X).
:-cora(T1),cora(T2),att(T1,id,X),att(T2,id,Y),eqo(X,Y),att(T1,title,S1),att(T2,title,S2),not sim(S1,S2).

#show.
#show (X,Y): att(V2,id,X),cora(V2), cora(V3), att(V3,id,Y), X!=Y, eqo(X,Y).


