movie(tid1).
movie(tid2).
movie(tid3).
movie(tid4).

cast(tid5).
cast(tid6).
cast(tid7).
cast(tid11).


review(tid8).
review(tid9).
review(tid10).



%% movie
att(tid1,mid,a).
att(tid2,mid,b).
att(tid3,mid,c).
att(tid4,mid,d).


att(tid1,title,t1).
att(tid2,title,t2).
att(tid3,title,t3).
att(tid4,title,t4).


att(tid1,cid,a1).
att(tid2,cid,a2).
att(tid3,cid,a3).
att(tid4,cid,a4).


att(tid1,rid,r1).
att(tid2,rid,r1).
att(tid3,rid,r2).
att(tid4,rid,r1).



%% cast
att(tid5,cid,a1).
att(tid6,cid,a2).
att(tid7,cid,a3).
att(tid11,cid,a4).

att(tid5,name,chloe1).
att(tid6,name,chloe2).
att(tid7,name,chloe3).
att(tid11,name,john).

sim(chloe1,chloe2).
sim(chloe2,chloe1).
sim(chloe1,chloe3).
sim(chloe3,chloe1).
sim(chloe2,chloe3).
sim(chloe3,chloe2).

att(tid5,gender,f).
att(tid6,gender,f).
att(tid7,gender,f).
att(tid11,gender,m).


% review
att(tid8,rid,r1).
att(tid9,rid,r2).
att(tid10,rid,r3).


att(tid8,score,10).
att(tid9,score,10).
att(tid10,score,8).


att(tid8,website,tomato).
att(tid9,website,tomato).
att(tid10,website,douban).



% similar title, and has author with similar names and the same review
