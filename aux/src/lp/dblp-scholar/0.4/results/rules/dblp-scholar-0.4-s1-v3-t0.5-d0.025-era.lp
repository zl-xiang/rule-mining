sim(X,X) :- att(T,Attr,X).
sim(X,Y):- sim(Y,X).
:- att(V2,did,X),dblp(V2),scholar(V3), att(V3,sid,Y), eqo(X,Y), att(V2,dtitle,VN1), att(V3,stitle,VN2), not sim(VN1,VN2).

#show.
#show (X,Y): att(V2,did,X),dblp(V2),scholar(V3), att(V3,sid,Y), eqo(X,Y), X!=Y.


sim(X,X):- att(T,A,X).
              sim(Y,X):- sim(X,Y).
              #show.
              #show (X,Y): att(V2,did,X),dblp(V2),scholar(V3), att(V3,sid,Y), eqo(X,Y), X!=Y.

activeo(V0,V1) :- att(V2,did,V0),dblp(V2),att(V2,dauthors,V5),att(V2,dyear,V4),sim(V5,V6),att(V3,sid,V1),scholar(V3),att(V3,syear,V4),att(V3,sauthors,V6).
activeo(V0,V1) :- att(V2,did,V0),dblp(V2),att(V2,dyear,V5),att(V2,dtitle,V4),sim(V4,V7),sim(V5,V6),att(V3,sid,V1),scholar(V3),att(V3,syear,V6),att(V3,stitle,V7).
activeo(V0,V1) :- att(V2,did,V0),dblp(V2),att(V2,dtitle,V5),att(V2,dauthors,V4),sim(V5,V6),sim(V4,V7),att(V3,sid,V1),scholar(V3),att(V3,stitle,V6),att(V3,sauthors,V7).
activeo(V0,V1) :- att(V2,did,V0),dblp(V2),att(V2,dauthors,V5),att(V2,dvenue,V4),sim(V4,V7),sim(V5,V6),att(V3,sid,V1),scholar(V3),att(V3,sauthors,V6),att(V3,svenue,V7).
activeo(V0,V1) :- att(V2,did,V0),dblp(V2),att(V2,dtitle,V5),att(V2,dvenue,V4),sim(V4,V7),sim(V5,V6),att(V3,sid,V1),scholar(V3),att(V3,stitle,V6),att(V3,svenue,V7).
