sim(X,X):- att(T,A,X). 
sim(Y,X):- sim(X,Y). 
eqo(X,X):-att(T,species,X).

eqo(V0,V1):- species(V3),att(V3,species,V1),att(V3,conquest_order,V4),species(V2),att(V2,species,V0),att(V2,conquest_order,V4).
eqo(V0,V1):- species(V3),att(V3,species,V1),att(V3,habitat,V5),att(V3,capture_rate,V4),species(V2),att(V2,capture_rate,V4),att(V2,habitat,V5),att(V2,species,V0).
eqo(V0,V1):- species(V2),att(V2,species,V0),att(V2,growth_rate,V6),att(V2,shape,V4),att(V2,hatch_counter,V7),att(V2,base_happiness,V5),species(V3),att(V3,growth_rate,V6),att(V3,shape,V4),att(V3,species,V1),att(V3,base_happiness,V5),att(V3,hatch_counter,V7).
eqo(V0,V1):- species(V2),att(V2,species,V0),att(V2,capture_rate,V6),att(V2,gender_rate,V7),att(V2,generation,V5),att(V2,hatch_counter,V4),species(V3),att(V3,generation,V5),att(V3,capture_rate,V6),att(V3,species,V1),att(V3,gender_rate,V7),att(V3,hatch_counter,V4).
eqo(V0,V1):- species(V2),att(V2,species,V0),att(V2,capture_rate,V6),att(V2,gender_rate,V7),att(V2,color,V4),att(V2,base_happiness,V5),species(V3),att(V3,capture_rate,V6),att(V3,species,V1),att(V3,base_happiness,V5),att(V3,color,V4),att(V3,gender_rate,V7).
