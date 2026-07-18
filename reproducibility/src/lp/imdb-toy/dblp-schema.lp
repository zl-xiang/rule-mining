schema(dblp_acm).
r(dblp_acm,dblp,5).
r(dblp_acm,acm,5).

% er_type: 4 - default, 2 - object, 3 - value
attr(a1,id,dblp,0,2).
attr(a2,title,dblp,1,4).
attr(a3,authors,dblp,2,4).
attr(a4,venue,dblp,3,4).
attr(a5,year,dblp,4,4).

attr(a6,id,acm,0,2).
attr(a7,title,acm,1,4).
attr(a8,authors,acm,2,4).
attr(a9,venue,acm,3,4).
attr(a10,year,acm,4,4).


compatible_attr(a1,a6).
compatible_attr(a2,a7).
compatible_attr(a3,a8).
compatible_attr(a4,a9).
compatible_attr(a5,a10).
