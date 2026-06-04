sim(X,X) :- att(T,Attr,X).
sim(X,Y):- sim(Y,X).
eqo(X,X):-att(T,species,X).


eqo(V0,V1):- species(V3),att(V3,species,V1),att(V3,has_gender_differences,V4),att(V3,growth_rate,V5),species(V2),att(V2,species,V0),att(V2,has_gender_differences,V4),att(V2,growth_rate,V5).
