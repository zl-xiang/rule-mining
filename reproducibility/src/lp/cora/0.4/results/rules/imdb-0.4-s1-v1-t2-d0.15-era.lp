sim(X,X) :- att(T,Attr,X).
sim(X,Y):- sim(Y,X).
:-cora(T1),cora(T2),att(T1,id,X),att(T2,id,X),att(T1,title,S1),att(T2,title,S2),not sim(S1,S2).


