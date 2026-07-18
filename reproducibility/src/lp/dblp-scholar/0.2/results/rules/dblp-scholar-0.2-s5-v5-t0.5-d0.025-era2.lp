sim(X,X) :- att(T,Attr,X).
sim(X,Y):- sim(Y,X).
:- att(V2,did,X),dblp(V2),scholar(V3), att(V3,sid,Y), eqo(X,Y), att(V2,dtitle,VN1), att(V3,stitle,VN2), not sim(VN1,VN2).
:- att(V2,did,X),dblp(V2),scholar(V3), att(V3,sid,Y), eqo(X,Y), att(V2,dauthors,VN1), att(V3,sauthors,VN2), not sim(VN1,VN2).

#show.
#show (X,Y): att(V2,did,X),dblp(V2),scholar(V3), att(V3,sid,Y), eqo(X,Y), X!=Y.


sim(X,X):- att(T,A,X).
              sim(Y,X):- sim(X,Y).
              #show.
              #show (X,Y): att(V2,did,X),dblp(V2),scholar(V3), att(V3,sid,Y), eqo(X,Y), X!=Y.

activeo(V0,V1) :- att(V2,did,V0),dblp(V2),att(V2,dauthors,V4),att(V3,sauthors,V4),scholar(V3),att(V3,sid,V1).
activeo(V0,V1) :- att(V3,sid,V1),scholar(V3),att(V3,svenue,V5),sim(V5,V4),att(V2,dvenue,V4),dblp(V2),att(V2,did,V0).
activeo(V0,V1) :- att(V3,sid,V1),scholar(V3),att(V3,stitle,V5),sim(V5,V4),att(V2,dtitle,V4),dblp(V2),att(V2,did,V0).
activeo(V0,V1) :- att(V3,sid,V1),scholar(V3),att(V3,sauthors,V7),att(V3,syear,V6),sim(V7,V5),sim(V6,V4),att(V2,dauthors,V5),dblp(V2),att(V2,dyear,V4),att(V2,did,V0).
