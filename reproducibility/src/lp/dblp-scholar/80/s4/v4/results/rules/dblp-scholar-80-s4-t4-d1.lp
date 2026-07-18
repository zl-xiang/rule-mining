sim(X,X):- att(T,A,X).
              sim(Y,X):- sim(X,Y).
              #show.
              #show (X,Y): att(V2,did,X),dblp(V2),scholar(V3), att(V3,sid,Y), eqo(X,Y), X!=Y.

eqo(V0,V1):- att(V2,did,V0),dblp(V2),att(V2,dtitle,V4),sim(V5,V4),att(V3,stitle,V5),scholar(V3),att(V3,sid,V1).
eqo(V0,V1):- att(V3,sid,V1),scholar(V3),att(V3,sauthors,V6),att(V3,syear,V4),sim(V6,V5),att(V2,dyear,V4),dblp(V2),att(V2,dauthors,V5),att(V2,did,V0).
eqo(V0,V1):- att(V3,sid,V1),scholar(V3),att(V3,sauthors,V7),att(V3,svenue,V6),sim(V7,V5),sim(V6,V4),att(V2,dauthors,V5),dblp(V2),att(V2,did,V0),att(V2,dvenue,V4).
