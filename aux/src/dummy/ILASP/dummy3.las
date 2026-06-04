
eq(X,Y):- eq(X,Z),eq(Z,Y).
eq(x1,x1).
eq(x2,x2).
eq(x3,x3).



r(x1,a1).
r(x2,a1).
r(x3,a2).
r(x4,a3).

sim(a2,a3).


#modeh(eq(var(x),var(x)),(symmetric,anti_reflexive)).
#modeb(2, r(var(x),var(a)), (positive)).
#modeb(sim(var(a),var(a)), (positive)).


#pos(s, {
  eq(x1, x2),
  eq(x3, x4)                 
}, { }).                           

#neg(s, {
  eq(x2, x3),
  eq(x1, x4)                 
}, { }).                           
       


#constant(x, x1).
#constant(x, x2).
#constant(x, x3).
#constant(x, x4).

#constant(a, a1).
#constant(a, a2).
#constant(a, a3).

#maxv(5).