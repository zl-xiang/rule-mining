
tuple(T1) :-
    cora(T1), 
    not cora_train(T1).


cora_test(T1):- tuple(T1),cora(T1).
att_test(T1,Attr,X):- tuple(T1), has_sort(cora,Attr),att(T1,Attr,X).




#show cora_test/1.
#show att_test/3.
