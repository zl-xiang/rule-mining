% schema info
schema(pokemon).
% pairwise.


% er_type: 4 - default, 2 - object, 3 - value, 0 - tid
% attributes here should be independent to relations
% species
attr(tid,0).
attr(species,2).
attr(generation,4).
% attr(evolves_from_species,2).
% attr(evolution_chain,4).
attr(color,4).
attr(shape,4).
attr(habitat,4).
attr(gender_rate,4).
attr(capture_rate,4).
attr(base_happiness,4).
attr(is_baby,4).
attr(hatch_counter,4).
attr(has_gender_differences,4).
attr(growth_rate,4).
attr(forms_switchable,4).
attr(is_legendary,4).
attr(is_mythical,4).
attr(conquest_order,4).

% species name
attr(local_language,4).
attr(name,4).
attr(genus,4).



% species description
attr(version,4).
attr(language,4).
attr(flavor_text,4).


compatible_attr(X,Y) :- compatible_attr(Y,X).
compatible_attr(X,Y) :- compatible_attr(X,Z), compatible_attr(Z,Y).
compatible_attr(X,X) :- attr(X,_), X!=tid.

r(pokemon,species,16). 
%r(imdb,name_basics,4).
r(pokemon,spec_name,5).
r(pokemon,spec_desc,5).



has_sort(species,species).
has_sort(species,generation).
% has_sort(species,evolution_chain).
has_sort(species,color).
has_sort(species,shape).
has_sort(species,habitat).
has_sort(species,gender_rate).
has_sort(species,capture_rate).
has_sort(species,base_happiness).
has_sort(species,is_baby).
has_sort(species,hatch_counter).
has_sort(species,has_gender_differences).
has_sort(species,growth_rate).
has_sort(species,forms_switchable).
has_sort(species,is_legendary).
has_sort(species,is_mythical).
has_sort(species,conquest_order).


has_sort(spec_name,species).
has_sort(spec_name,local_language).
has_sort(spec_name,name).
has_sort(spec_name,genus).

has_sort(spec_desc,species).
has_sort(spec_desc,version).
has_sort(spec_desc,language).
has_sort(spec_desc,flavor_text).



% language constructs
head_pred(eqo,2).

body_pred(sim,2).
body_pred(att,3).
% body_pred(range,2).

body_pred(R,1):- r(S,R,A). 
const(att,2).


{type(eqo,(Aname1,Aname2));type(sim,(Aname1,Aname2))}=2 :- compatible_attr(Aname1,Aname2).


type(R,(tid)) :- r(_,R,_). 

% shall tid be a unified attribute?
type(att,(tid,attr,Aname)):- attr(Aname,_), Aname!= tid.
% type(range,(tid,relation)).

target(species,species,0).
target(species,species,1).

max_body(12).
max_vars(12).



