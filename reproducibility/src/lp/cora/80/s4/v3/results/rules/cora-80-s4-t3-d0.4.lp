sim(X,X) :- att(T,Attr,X).
sim(X,Y):- sim(Y,X).


#show.
#show (X,Y): att(V2,id,X),cora(V2), cora(V3), att(V3,id,Y), X!=Y, eqo(X,Y).

eqo(V0,V1):- att(V2,id,V0),cora(V2),att(V2,pages,V4),att(V3,pages,V4),cora(V3),att(V3,id,V1).
eqo(V0,V1):- att(V2,id,V0),cora(V2),att(V2,date,V4),sim(V5,V4),att(V3,date,V5),cora(V3),att(V3,id,V1).
eqo(V0,V1):- att(V2,id,V0),cora(V2),att(V2,institution,V4),sim(V5,V4),att(V3,id,V1),cora(V3),att(V3,institution,V5).
eqo(V0,V1):- att(V3,id,V1),cora(V3),att(V3,title,V4),att(V3,year,V6),sim(V6,V5),att(V2,year,V5),cora(V2),att(V2,title,V4),att(V2,id,V0).
eqo(V0,V1):- att(V3,id,V1),cora(V3),att(V3,journal,V4),att(V3,year,V6),sim(V6,V5),att(V2,year,V5),cora(V2),att(V2,journal,V4),att(V2,id,V0).
eqo(V0,V1):- att(V3,id,V1),cora(V3),att(V3,title,V6),att(V3,authors,V4),sim(V5,V6),att(V2,title,V5),cora(V2),att(V2,authors,V4),att(V2,id,V0).
eqo(V0,V1):- att(V3,id,V1),cora(V3),att(V3,title,V4),att(V3,journal,V6),sim(V6,V5),att(V2,journal,V5),cora(V2),att(V2,title,V4),att(V2,id,V0).
eqo(V0,V1):- att(V3,id,V1),cora(V3),att(V3,authors,V6),att(V3,journal,V4),sim(V6,V5),att(V2,authors,V5),cora(V2),att(V2,journal,V4),att(V2,id,V0).
eqo(V0,V1):- att(V3,id,V1),cora(V3),att(V3,title,V4),att(V3,authors,V6),sim(V6,V5),att(V2,authors,V5),cora(V2),att(V2,title,V4),att(V2,id,V0).
eqo(V0,V1):- att(V3,id,V1),cora(V3),att(V3,booktitle,V6),att(V3,address,V7),sim(V5,V7),sim(V4,V6),att(V2,booktitle,V4),cora(V2),att(V2,address,V5),att(V2,id,V0).
eqo(V0,V1):- att(V3,id,V1),cora(V3),att(V3,booktitle,V6),att(V3,authors,V7),sim(V5,V6),sim(V4,V7),att(V2,booktitle,V5),cora(V2),att(V2,authors,V4),att(V2,id,V0).
eqo(V0,V1):- att(V3,id,V1),cora(V3),att(V3,authors,V7),att(V3,year,V6),sim(V5,V6),sim(V4,V7),att(V2,year,V5),cora(V2),att(V2,authors,V4),att(V2,id,V0).
eqo(V0,V1):- att(V3,id,V1),cora(V3),att(V3,title,V6),att(V3,booktitle,V7),sim(V6,V5),sim(V4,V7),att(V2,title,V5),cora(V2),att(V2,booktitle,V4),att(V2,id,V0).
eqo(V0,V1):- att(V3,id,V1),cora(V3),att(V3,editor,V7),att(V3,title,V6),sim(V6,V5),sim(V4,V7),att(V2,title,V5),cora(V2),att(V2,editor,V4),att(V2,id,V0).
eqo(V0,V1):- att(V3,id,V1),cora(V3),att(V3,address,V7),att(V3,year,V6),sim(V5,V7),sim(V4,V6),att(V2,address,V5),cora(V2),att(V2,year,V4),att(V2,id,V0).
eqo(V0,V1):- att(V3,id,V1),cora(V3),att(V3,authors,V7),att(V3,pages,V6),sim(V5,V6),sim(V4,V7),att(V2,pages,V5),cora(V2),att(V2,authors,V4),att(V2,id,V0).
eqo(V0,V1):- att(V3,id,V1),cora(V3),att(V3,authors,V6),att(V3,address,V7),sim(V5,V7),sim(V4,V6),att(V2,address,V5),cora(V2),att(V2,authors,V4),att(V2,id,V0).
eqo(V0,V1):- att(V3,id,V1),cora(V3),att(V3,title,V6),att(V3,publisher,V7),sim(V6,V5),sim(V4,V7),att(V2,title,V5),cora(V2),att(V2,publisher,V4),att(V2,id,V0).
eqo(V0,V1):- att(V3,id,V1),cora(V3),att(V3,title,V6),att(V3,address,V7),sim(V5,V7),sim(V4,V6),att(V2,address,V5),cora(V2),att(V2,title,V4),att(V2,id,V0).
eqo(V0,V1):- att(V3,id,V1),cora(V3),att(V3,publisher,V7),att(V3,pages,V6),sim(V6,V5),sim(V4,V7),att(V2,pages,V5),cora(V2),att(V2,publisher,V4),att(V2,id,V0).
eqo(V0,V1):- att(V3,id,V1),cora(V3),att(V3,year,V6),att(V3,pages,V7),sim(V6,V5),sim(V4,V7),att(V2,year,V5),cora(V2),att(V2,pages,V4),att(V2,id,V0).
eqo(V0,V1):- att(V3,id,V1),cora(V3),att(V3,publisher,V7),att(V3,year,V6),sim(V6,V5),sim(V4,V7),att(V2,year,V5),cora(V2),att(V2,publisher,V4),att(V2,id,V0).
eqo(V0,V1):- att(V3,id,V1),cora(V3),att(V3,authors,V7),att(V3,editor,V6),sim(V5,V6),sim(V4,V7),att(V2,editor,V5),cora(V2),att(V2,authors,V4),att(V2,id,V0).
eqo(V0,V1):- att(V3,id,V1),cora(V3),att(V3,publisher,V7),att(V3,editor,V6),sim(V6,V5),sim(V4,V7),att(V2,publisher,V4),cora(V2),att(V2,editor,V5),att(V2,id,V0).
eqo(V0,V1):- att(V3,id,V1),cora(V3),att(V3,booktitle,V6),att(V3,publisher,V7),sim(V6,V5),sim(V4,V7),att(V2,publisher,V4),cora(V2),att(V2,booktitle,V5),att(V2,id,V0).
eqo(V0,V1):- att(V3,id,V1),cora(V3),att(V3,authors,V7),att(V3,publisher,V6),sim(V5,V6),sim(V4,V7),att(V2,publisher,V5),cora(V2),att(V2,authors,V4),att(V2,id,V0).
eqo(V0,V1):- att(V3,id,V1),cora(V3),att(V3,title,V6),att(V3,pages,V7),sim(V6,V5),sim(V4,V7),att(V2,title,V5),cora(V2),att(V2,pages,V4),att(V2,id,V0).
