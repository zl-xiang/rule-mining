sim(X,X) :- att(T,Attr,X).
sim(X,Y):- sim(Y,X).
:-cora(T1),cora(T2),att(T1,id,X),att(T2,id,Y),eqo(X,Y),att(T1,title,S1),att(T2,title,S2),not sim(S1,S2).

#show.
#show (X,Y): att(V2,id,X),cora(V2), cora(V3), att(V3,id,Y), X!=Y, eqo(X,Y).


sim(X,X) :- att(T,Attr,X).
sim(X,Y):- sim(Y,X).


#show.
#show (X,Y): att(V2,id,X),cora(V2), cora(V3), att(V3,id,Y), X!=Y, eqo(X,Y).

activeo(V0,V1) :- att(V3,id,V1),cora(V3),att(V3,title,V5),att(V3,year,V4),att(V2,title,V5),att(V2,year,V4),cora(V2),att(V2,id,V0).
activeo(V0,V1) :- att(V3,id,V1),cora(V3),att(V3,title,V5),att(V3,pages,V6),sim(V4,V6),att(V2,pages,V4),att(V2,title,V5),cora(V2),att(V2,id,V0).
activeo(V0,V1) :- att(V3,id,V1),cora(V3),att(V3,journal,V5),att(V3,pages,V6),sim(V4,V6),att(V2,pages,V4),cora(V2),att(V2,journal,V5),att(V2,id,V0).
activeo(V0,V1) :- att(V3,id,V1),cora(V3),att(V3,authors,V5),att(V3,journal,V6),sim(V4,V6),att(V2,journal,V4),cora(V2),att(V2,id,V0),att(V2,authors,V5).
activeo(V0,V1) :- att(V3,id,V1),cora(V3),att(V3,year,V7),att(V3,pages,V6),sim(V7,V5),sim(V4,V6),att(V2,pages,V4),cora(V2),att(V2,id,V0),att(V2,year,V5).
activeo(V0,V1) :- att(V3,id,V1),cora(V3),att(V3,date,V7),att(V3,pages,V6),sim(V7,V5),sim(V4,V6),att(V2,pages,V4),cora(V2),att(V2,id,V0),att(V2,date,V5).
activeo(V0,V1) :- att(V3,id,V1),cora(V3),att(V3,date,V7),att(V3,editor,V6),sim(V7,V4),sim(V5,V6),att(V2,editor,V5),att(V2,date,V4),cora(V2),att(V2,id,V0).
activeo(V0,V1) :- att(V3,id,V1),cora(V3),att(V3,authors,V7),att(V3,journal,V4),att(V3,date,V6),sim(V7,V5),att(V2,journal,V4),cora(V2),att(V2,id,V0),att(V2,date,V6),att(V2,authors,V5).
activeo(V0,V1) :- att(V3,id,V1),cora(V3),att(V3,journal,V5),att(V3,title,V7),att(V3,year,V4),sim(V7,V6),att(V2,title,V6),att(V2,year,V4),att(V2,journal,V5),cora(V2),att(V2,id,V0).
activeo(V0,V1) :- att(V3,id,V1),cora(V3),att(V3,authors,V7),att(V3,journal,V6),att(V3,year,V4),sim(V7,V5),att(V2,journal,V6),att(V2,year,V4),cora(V2),att(V2,id,V0),att(V2,authors,V5).
activeo(V0,V1) :- att(V3,id,V1),cora(V3),att(V3,authors,V7),att(V3,journal,V4),att(V3,title,V6),sim(V7,V5),att(V2,journal,V4),cora(V2),att(V2,id,V0),att(V2,title,V6),att(V2,authors,V5).
