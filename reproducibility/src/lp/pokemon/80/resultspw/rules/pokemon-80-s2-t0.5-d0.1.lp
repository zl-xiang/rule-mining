sim(X,X):- att(T,A,X). 
sim(Y,X):- sim(X,Y). 
eqo(X,X):-att(T,species,X).

eqo(V0,V1):- species(V3),att(V3,species,V1),att(V3,conquest_order,V4),species(V2),att(V2,conquest_order,V4),att(V2,species,V0).
eqo(V0,V1):- species(V3),att(V3,species,V1),att(V3,capture_rate,V4),att(V3,color,V5),species(V2),att(V2,capture_rate,V4),att(V2,species,V0),att(V2,color,V5).
eqo(V0,V1):- species(V3),att(V3,species,V1),att(V3,habitat,V5),att(V3,capture_rate,V4),att(V3,growth_rate,V6),species(V2),att(V2,habitat,V5),att(V2,growth_rate,V6),att(V2,capture_rate,V4),att(V2,species,V0).
eqo(V0,V1):- species(V3),att(V3,species,V1),att(V3,generation,V4),att(V3,capture_rate,V6),att(V3,gender_rate,V5),species(V2),att(V2,gender_rate,V5),att(V2,species,V0),att(V2,generation,V4),att(V2,capture_rate,V6).
eqo(V0,V1):- species(V3),att(V3,species,V1),att(V3,capture_rate,V5),att(V3,shape,V6),att(V3,gender_rate,V4),species(V2),att(V2,capture_rate,V5),att(V2,species,V0),att(V2,shape,V6),att(V2,gender_rate,V4).
