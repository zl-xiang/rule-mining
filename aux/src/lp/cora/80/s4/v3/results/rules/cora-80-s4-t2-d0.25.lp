sim(X,X) :- att(T,Attr,X).
sim(X,Y):- sim(Y,X).


#show.
#show (X,Y): att(V2,id,X),cora(V2), cora(V3), att(V3,id,Y), X!=Y, eqo(X,Y).

eqo(V0,V1):- att(V3,id,V1),cora(V3),att(V3,authors,V4),att(V3,year,V6),sim(V6,V5),att(V2,authors,V4),att(V2,id,V0),cora(V2),att(V2,year,V5).
eqo(V0,V1):- att(V3,id,V1),cora(V3),att(V3,pages,V5),att(V3,journal,V6),sim(V4,V6),att(V2,journal,V4),att(V2,pages,V5),att(V2,id,V0),cora(V2).
eqo(V0,V1):- att(V3,id,V1),cora(V3),att(V3,date,V5),att(V3,journal,V6),sim(V4,V6),att(V2,journal,V4),att(V2,date,V5),att(V2,id,V0),cora(V2).
eqo(V0,V1):- att(V3,id,V1),cora(V3),att(V3,journal,V5),att(V3,pages,V6),sim(V4,V6),att(V2,id,V0),att(V2,pages,V4),att(V2,journal,V5),cora(V2).
eqo(V0,V1):- att(V3,id,V1),cora(V3),att(V3,authors,V5),att(V3,pages,V6),sim(V4,V6),att(V2,authors,V5),att(V2,id,V0),att(V2,pages,V4),cora(V2).
eqo(V0,V1):- att(V3,id,V1),cora(V3),att(V3,authors,V5),att(V3,title,V6),sim(V4,V6),att(V2,authors,V5),att(V2,title,V4),att(V2,id,V0),cora(V2).
eqo(V0,V1):- att(V3,id,V1),cora(V3),att(V3,title,V5),att(V3,pages,V6),sim(V4,V6),att(V2,title,V5),att(V2,id,V0),att(V2,pages,V4),cora(V2).
eqo(V0,V1):- att(V3,id,V1),cora(V3),att(V3,booktitle,V6),att(V3,date,V7),sim(V5,V7),sim(V4,V6),att(V2,booktitle,V4),att(V2,date,V5),att(V2,id,V0),cora(V2).
eqo(V0,V1):- att(V3,id,V1),cora(V3),att(V3,date,V7),att(V3,publisher,V6),sim(V5,V7),sim(V4,V6),att(V2,date,V5),att(V2,id,V0),att(V2,publisher,V4),cora(V2).
eqo(V0,V1):- att(V3,id,V1),cora(V3),att(V3,year,V7),att(V3,address,V6),sim(V4,V6),sim(V5,V7),att(V2,id,V0),cora(V2),att(V2,address,V4),att(V2,year,V5).
eqo(V0,V1):- att(V3,id,V1),cora(V3),att(V3,title,V7),att(V3,publisher,V6),sim(V4,V6),sim(V5,V7),att(V2,id,V0),att(V2,publisher,V4),cora(V2),att(V2,title,V5).
eqo(V0,V1):- att(V3,id,V1),cora(V3),att(V3,date,V6),att(V3,pages,V7),sim(V5,V7),sim(V4,V6),att(V2,pages,V5),att(V2,id,V0),att(V2,date,V4),cora(V2).
eqo(V0,V1):- att(V3,id,V1),cora(V3),att(V3,editor,V6),att(V3,title,V7),sim(V4,V6),sim(V5,V7),att(V2,editor,V4),att(V2,id,V0),cora(V2),att(V2,title,V5).
eqo(V0,V1):- att(V3,id,V1),cora(V3),att(V3,title,V7),att(V3,booktitle,V6),sim(V4,V6),sim(V5,V7),att(V2,booktitle,V4),att(V2,id,V0),cora(V2),att(V2,title,V5).
eqo(V0,V1):- att(V3,id,V1),cora(V3),att(V3,date,V6),att(V3,institution,V7),sim(V5,V7),sim(V4,V6),att(V2,institution,V5),att(V2,id,V0),att(V2,date,V4),cora(V2).
eqo(V0,V1):- att(V3,id,V1),cora(V3),att(V3,authors,V6),att(V3,editor,V7),sim(V5,V7),sim(V4,V6),att(V2,editor,V5),att(V2,authors,V4),att(V2,id,V0),cora(V2).
eqo(V0,V1):- att(V3,id,V1),cora(V3),att(V3,institution,V6),att(V3,year,V7),sim(V4,V6),sim(V5,V7),att(V2,id,V0),cora(V2),att(V2,year,V5),att(V2,institution,V4).
eqo(V0,V1):- att(V3,id,V1),cora(V3),att(V3,year,V7),att(V3,pages,V6),sim(V4,V6),sim(V5,V7),att(V2,id,V0),cora(V2),att(V2,pages,V4),att(V2,year,V5).
eqo(V0,V1):- att(V3,id,V1),cora(V3),att(V3,authors,V7),att(V3,title,V6),att(V3,journal,V4),sim(V7,V5),att(V2,journal,V4),att(V2,authors,V5),att(V2,title,V6),att(V2,id,V0),cora(V2).
eqo(V0,V1):- att(V3,id,V1),cora(V3),att(V3,authors,V7),att(V3,year,V5),att(V3,journal,V4),sim(V7,V6),att(V2,journal,V4),att(V2,id,V0),att(V2,authors,V6),cora(V2),att(V2,year,V5).
eqo(V0,V1):- att(V3,id,V1),cora(V3),att(V3,journal,V7),att(V3,title,V6),att(V3,year,V4),sim(V5,V7),att(V2,title,V6),att(V2,year,V4),att(V2,id,V0),cora(V2),att(V2,journal,V5).
eqo(V0,V1):- att(V3,id,V1),cora(V3),att(V3,authors,V7),att(V3,year,V5),att(V3,publisher,V4),sim(V7,V6),att(V2,id,V0),att(V2,publisher,V4),att(V2,authors,V6),cora(V2),att(V2,year,V5).
eqo(V0,V1):- att(V3,id,V1),cora(V3),att(V3,journal,V5),att(V3,title,V7),att(V3,year,V4),sim(V6,V7),att(V2,title,V6),att(V2,year,V4),att(V2,id,V0),cora(V2),att(V2,journal,V5).
eqo(V0,V1):- att(V3,id,V1),cora(V3),att(V3,authors,V7),att(V3,title,V6),att(V3,year,V4),sim(V5,V7),att(V2,authors,V5),att(V2,title,V6),att(V2,year,V4),att(V2,id,V0),cora(V2).
