schema(dblp_scholar).
r(dblp_scholar,dblp,5).
r(dblp_scholar,scholar,5).

% er_type: 4 - default, 2 - object, 3 - value
attr(a1,id,dblp,0,2).
attr(a2,title,dblp,1,4).
attr(a3,authors,dblp,2,4).
attr(a4,venue,dblp,3,4).
attr(a5,year,dblp,4,4).

attr(a6,id,scholar,0,2).
attr(a7,title,scholar,1,4).
attr(a8,authors,scholar,2,4).
attr(a9,venue,scholar,3,4).
attr(a10,year,scholar,4,4).


compatible_attr(a1,a6).
compatible_attr(a2,a7).
compatible_attr(a3,a8).
compatible_attr(a4,a9).
compatible_attr(a5,a10).
