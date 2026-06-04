sim(X,X) :- att(T,Attr,X).
sim(X,Y):- sim(Y,X).
eqo(X,X):-att(T,species,X).


eqo(V0,V1):- species(V2),att(V2,species,V0),att(V2,capture_rate,V4),att(V2,hatch_counter,V5),species(V3),att(V3,species,V1),att(V3,capture_rate,V4),att(V3,hatch_counter,V5).
