sim(X,X) :- att(T,Attr,X).
sim(X,Y):- sim(Y,X).
eqo(X,X):-att(T,species,X).
:- eqo(X,Y), species(T1), species(T2), att(T1,species,X), att(T2,species,Y), spec_name(T3), spec_name(T4), att(T3,species,X), att(T4,species,Y),  att(T3,name,N1), att(T4,name,N2),  att(T3,local_language,LL), att(T4,local_language,LL),  not sim(N1,N2).
%:- eqo(X,Y), species(T1), species(T2), att(T1,species,X), att(T2,species,Y),  att(T1,color,C1), att(T2,color,C2), C1!=C2.



sim(X,X) :- att(T,Attr,X).
sim(X,Y):- sim(Y,X).
activeo(X,X) :-att(T,species,X).


activeo(V0,V1) :- species(V3),att(V3,species,V1),att(V3,has_gender_differences,V4),att(V3,growth_rate,V5),species(V2),att(V2,species,V0),att(V2,has_gender_differences,V4),att(V2,growth_rate,V5).
