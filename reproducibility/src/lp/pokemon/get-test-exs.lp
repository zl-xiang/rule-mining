
pos_test(eqo(X,Y)) :-
    title_basics(T1), att(T1,tconst,X), pos(eqo(X,Y)).
pos_test(eqo(X,Y)) :-
    title_basics(T1), att(T1,tconst,Y), pos(eqo(X,Y)).

#show pos_test/1.