
tuple(T1) :-
    dblp(T1), 
    not dblp_train(T1).

tuple(T1) :-
    scholar(T1), 
    not scholar_train(T1).


dblp_test(T1):- tuple(T1),dblp(T1).
att_test(T1,Attr,X):- tuple(T1), has_sort(dblp,Attr),att(T1,Attr,X).


scholar_test(T1):- tuple(T1),scholar(T1).
att_test(T1,Attr,X):- tuple(T1), has_sort(scholar,Attr),att(T1,Attr,X).


#show dblp_test/1.
#show scholar_test/1.
#show att_test/3.
