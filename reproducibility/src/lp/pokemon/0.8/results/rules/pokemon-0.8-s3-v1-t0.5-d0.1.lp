sim(X,X) :- att(T,Attr,X).
sim(X,Y):- sim(Y,X).
eqo(X,X):-att(T,species,X).


eqo(V0,V1):- species(V3),att(V3,species,V1),species(V2),att(V2,species,V0),att(V5,species,V1),spec_name(V5),att(V5,name,V7),sim(V6,V7),att(V4,name,V6),spec_name(V4),att(V4,species,V0).
