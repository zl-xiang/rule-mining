eqo(X,Y):- pos(eqo(X,Y)).
eqo(X,Y):- neg(eqo(X,Y)).


tuple(T1) :-
    cora(T1), 
    att(T1,id,X),
    eqo(X,_).


tuple(T1) :-
    cora(T1), 
    att(T1,id,X),
    eqo(_,X).


cora_train(T1):- tuple(T1),cora(T1).
att_train(T1,Attr,X):- tuple(T1), has_sort(cora,Attr),att(T1,Attr,X).



#show cora_train/1.
#show att_train/3.
