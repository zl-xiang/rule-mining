% schema info
schema(cora).

% er_type: 4 - default, 2 - object, 3 - value, 0 - tid
% attributes here should be independent to relations
attr(tid,0).
attr(address,3).
attr(authors,3).
attr(booktitle,3).
attr(date,3).
attr(editor,3).
attr(id,2).
attr(institution,3).
attr(journal,3).
%attr(month,3).
%attr(note,3).
attr(pages,3).
attr(publisher,3).
%attr(tech,3).
attr(title,3).
%attr(type,3).
attr(volume,3).
attr(year,3).


compatible_attr(X,Y) :- compatible_attr(Y,X).
compatible_attr(X,Y) :- compatible_attr(X,Z), compatible_attr(Z,Y).
compatible_attr(X,X) :- attr(X,_).

r(cora,cora,17).


has_sort(cora,address).
has_sort(cora,authors).
has_sort(cora,booktitle).
has_sort(cora,date).
has_sort(cora,editor).
has_sort(cora,id).
has_sort(cora,institution).
has_sort(cora,journal).
%has_sort(cora,month).
%has_sort(cora,note).
has_sort(cora,pages).
has_sort(cora,publisher).
%has_sort(cora,tech).
has_sort(cora,title).
%has_sort(cora,type).
has_sort(cora,volume).
has_sort(cora,year).




% language constructs
head_pred(eqo,2).

body_pred(cora,1).
body_pred(sim,2).
body_pred(att,3).



head_pred(eqo,2).


% body_pred(range,2).

body_pred(R,1):- r(S,R,A). 
const(att,2).


{type(eqo,(Aname1,Aname2));type(sim,(Aname1,Aname2))}=2 :- compatible_attr(Aname1,Aname2).


type(R,(tid)) :- r(_,R,_). 

% shall tid be a unified attribute?
type(att,(tid,attr,Aname)):- attr(Aname,_), Aname!= tid.
% type(range,(tid,relation)).


target(cora,id,0).
target(cora,id,1).
max_body(10).
max_vars(8).


pairwise.