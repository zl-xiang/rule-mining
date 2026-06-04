eq(X,Y):- eq(X,Z),eq(Z,Y).


eq(x1,x1).
eq(x2,x2).
eq(x3,x3).
eq(x4,x4).

r(x1,a1,b1).
r(x2,a1,b2).
r(x3,a2,b1).
r(x4,a3,b3).

sim(a2,a3).
sim(b1,b3).
sim(b1,b2).



#pos(s, {
  eq(x1, x2),          
  eq(x3, x4)                  
}, { }).                           
                             



#modeh(eq(var(x),var(x)),(symmetric)).

#modeb(r(var(x),var(a),var(b)),(positive)).

#modeb(sim(var(a),var(a)),(positive,symmetric)).
#modeb(sim(var(b),var(b)),(positive,symmetric)).

#constant(x, x1).
#constant(x, x2).
#constant(x, x3).
#constant(x, x4).


#constant(a, a1).
#constant(a, a2).
#constant(a, a3).

#constant(b, b1).
#constant(b, b2).
#constant(b, b3).


#maxv(7).