
pos_test(eqo(X,Y)) :-
    dblp_test(T1), att_test(T1,did,X), pos(eqo(X,Y)), scholar_test(T2), att_test(T2,sid,Y).

#show pos_test/1.