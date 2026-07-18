eqo(X,Y):- pos(eqo(X,Y)).
eqo(X,Y):- neg(eqo(X,Y)).


tuple(T1) :-
    species(T1), 
    att(T1,species,X),
    eqo(X,_).

tuple(T1) :-
    species(T1), 
    att(T1,species,Y),
    eqo(_,Y).

tuple(T1) :-
    spec_name(T1), 
    att(T1,species,Y),
    eqo(_,Y).

tuple(T1) :-
    spec_name(T1), 
    att(T1,species,X),
    eqo(X,_).

tuple(T1) :-
    spec_desc(T1), 
    att(T1,species,X),
    eqo(X,_).

tuple(T1) :-
    spec_desc(T1), 
    att(T1,species,Y),
    eqo(_,Y).


species_train(T1):- tuple(T1),species(T1).
att_train(T1,Attr,X):- tuple(T1), has_sort(species,Attr),att(T1,Attr,X).


spec_desc_train(T1):- tuple(T1),spec_desc(T1).
att_train(T1,Attr,X):- tuple(T1), has_sort(spec_desc,Attr),att(T1,Attr,X).


spec_name_train(T1):- tuple(T1),spec_name(T1).
att_train(T1,Attr,X):- tuple(T1), has_sort(spec_name,Attr),att(T1,Attr,X).


#show species_train/1.
#show spec_desc_train/1.
#show spec_name_train/1.
#show att_train/3.
