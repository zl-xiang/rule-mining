eqo(X,Y):- pos(eqo(X,Y)).
eqo(X,Y):- neg(eqo(X,Y)).


tuple(T1) :-
    dblp(T1), 
    att(T1,did,X),
    eqo(X,_).

tuple(T1) :-
    scholar(T1), 
    att(T1,sid,Y),
    eqo(_,Y).


dblp_train(T1):- tuple(T1),dblp(T1).
att_train(T1,Attr,X):- tuple(T1), has_sort(dblp,Attr),att(T1,Attr,X).


scholar_train(T1):- tuple(T1),scholar(T1).
att_train(T1,Attr,X):- tuple(T1), has_sort(scholar,Attr),att(T1,Attr,X).


#show dblp_train/1.
#show scholar_train/1.
#show att_train/3.
