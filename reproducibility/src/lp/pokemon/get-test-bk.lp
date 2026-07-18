
tuple(T1) :-
    title_basics(T1), 
    not title_basics_train(T1).

tuple(T1) :-
    title_akas(T1), 
    not title_akas_train(T1).

tuple(T1) :-
    title_ratings(T1), 
    not title_ratings_train(T1).

tuple(T1) :-
    title_principals(T1), 
    not title_principals_train(T1).


title_basics_test(T1):- tuple(T1),title_basics(T1).
att_test(T1,Attr,X):- tuple(T1), has_sort(title_basics,Attr),att(T1,Attr,X).


title_ratings_test(T1):- tuple(T1),title_ratings(T1).
att_test(T1,Attr,X):- tuple(T1), has_sort(title_ratings,Attr),att(T1,Attr,X).


title_akas_test(T1):- tuple(T1),title_akas(T1).
att_test(T1,Attr,X):- tuple(T1), has_sort(title_akas,Attr),att(T1,Attr,X).

title_principals_test(T1):- tuple(T1),title_principals(T1).
att_test(T1,Attr,X):- tuple(T1), has_sort(title_principals,Attr),att(T1,Attr,X).

#show title_principals_test/1.
#show title_basics_test/1.
#show title_akas_test/1.
#show title_ratings_test/1.
#show att_test/3.
