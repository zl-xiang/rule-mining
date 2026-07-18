sim(X,X):- att(T,A,X). 
sim(Y,X):- sim(X,Y). 
eqo(X,X):-att(T,species,X).

eqo(V0,V1):- species(V3),att(V3,species,V1),att(V3,hatch_counter,V6),att(V3,base_happiness,V4),att(V3,capture_rate,V7),att(V3,gender_rate,V5),species(V2),att(V2,hatch_counter,V6),att(V2,species,V0),att(V2,gender_rate,V5),att(V2,base_happiness,V4),att(V2,capture_rate,V7).
