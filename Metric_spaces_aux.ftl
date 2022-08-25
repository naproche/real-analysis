[read real-analysis/vocabulary.ftl]
[read vocabulary.ftl]
[read macros.ftl]

[synonym field/-s]

[prove off][read real-analysis/numbers.ftl][prove on]

Signature. Let p,q be elements. d(p,q) is a real number.

Definition 2_15. A metric space is a set X such that for every element p, q, r of X
  ((if p != q then d(p,q) > 0) and
  d(p,p) = 0 and
  d(p,q) = d(q,p) and
  d(p,q) <= d(p,r) + d(r,q)).

Axiom 2_16. Let X be a metric space. Let Y be a subset of X. Then Y is a metric space.

Definition 2_17_a. Let a and b be real numbers such that a < b. Seg(a,b)= {x | (x is a real number) and (x>a) 
and (x< b)}.

Definition 2_17_b. Let a and b be real numbers such that a < b. Int(a,b)= {x | (x is a real number) and (x>=a) 
and (x<=b)}.

Definition 2_18_a. Let X be a metric space. Let p be an element of X. Let r be a positive real number.
Neigh(p,r,X)={q| (q is an element of X) and (d(p,q)< r)}.

Definition 2_18_b. Let X be a metric space. Let Y be a subset of X. Let p be an element of X.
p is limit point of Y in X iff (for every positive real number r there exists an element q of Neigh(p,r,X)
such that (q!=p) and ( q is an element of Y)).

Definition 2_18_c.  Let X be a metric space. Let Y be a subset of X. Let p be an element of X.
p is isolated in Y inside X iff ((p is an element of Y) and (p is not limit point of Y in X)).

Definition 2_18_d.  Let X be a metric space. Let Y be a subset of X.
Y is closed in X iff (for every element p of X such that (p is limit point of Y in X) 
p is an element of Y).

Definition 2_18_e.  Let X be a metric space. Let Y be a subset of X. Let p be an element of X.
p is interior point of Y in X iff (there exists a positive real number r such that Neigh(p,r,X) 
is a subset of Y).

Definition 2_18_f. Let X be a metric space. Let Y be a subset of X. Y is open in X iff (for every
element p of Y p is interior point of Y in X). 

Definition 2_18_g. Let X be a metric space. Let Y be a subset of X. Compl(Y,X)={x| (x is an element of X)
and (x is not an element of Y)}.

Definition 2_18_h. Let X be a metric space. Let Y be a subset of X. Y is perfect in X iff (Y is
closed in X) and (for every element p of Y p is limit point of Y in X).

Definition 2_18_i1. Let X be a metric space. Let Y be a subset of X. Let M be a positive real number.
Y is bounded in X by M iff for every elements p, q of Y d(p,q)<=M.

Definition 2_18_i2. Let X be a metric space. Let Y be a subset of X. Y is bounded in X iff there exists
a positive real number M such that Y is bounded in X by M.

Definition 2_18_j. Let X be a metric space. Let Y be a subset of X. Y is dense in X iff 
for every element p of X we have (p is  limit point of Y in X) or (p is an element of Y).

Axiom 2_19. Let X be a metric space. Let r be a positive real number. Let p be an element of X. Neigh(p,r,X)
is open in X. 

Definition.A natural number is an integer k such that k=0 or 0<k .
Definition. Let x and y be real numbers. x =< y iff x=y or x<y.
Let n denote a natural number.

Signature.Let x be a real number. abs(x) is a real number.
Axiom. Let x be a positive real number. abs(x) = x.
Axiom. abs(0)=0.
Axiom. Let x be a negative real number. abs(x)=-x.
Axiom. For every real number x 0=<abs(x).

Axiom. Let x,y be real numbers.abs(x+y)=< abs(x)+abs(y).

Definition Dist. Let x and y be real numbers. dist(x,y)=abs(x-y).

Axiom. Let f be a map. Dom(f) is a set. 

Definition ImOfSubset.  Let f be a map. Let E be a subset of Dom(f). 
Im(E,f) is a set such that Im(E,f) = { f(x)  | x is an element of E}.

Definition SurjectiveToB.Let B be a set. Let f be a map.
f is surjective onto B iff  Im(Dom(f),f) = B and for every element x of Dom(f) f(x) is an element of B.

Definition Preimage. Let f be a map. Let E be a nonempty subset of Im(Dom(f),f). 
ImInv(E,f) is a nonempty subset  of Dom(f) such that #we need this detail to ensure this is a set and that it is nonempty.
ImInv(E,f) = {x | x is an element of Dom(f) and f(x) is an element of E}.

Definition Injective. Let f be a map. f is injective iff for every element x 
of Dom(f) and every element y of Dom(f) (if f(x) = f(y) then x = y).

Definition BijectionToB. Let B be a set. Let f be a map.
f is bijective onto B iff (f is injective and f is surjective onto B).

Definition Equipotency. Let A and B be sets. A and B are equipotent iff there exists a map
f such that (Dom(f)=A and f is bijective onto B).

Definition BiggerSet. Let A and B be sets. A is bigger than B iff there exists a map f such that
(Dom(f)=A and f is surjective onto B and for every element a of A f(a) is an element of B).

Definition FinNAT.Fin(n) is a set such that Fin(n) = {x | x is a natural number and x<n}.

Definition Finite. Let A be a set. A is finite iff (there exists n such that Fin(n)
is bigger than A) or (A is an empty set).

Axiom. Let n be a natural number. Fin(n) is finite.

Definition Infinite. Let A be a set. A is infinite iff A is not finite. 

Definition UnionWithBound. Let X be a set. Let C be a set such that all elements of C are subsets
of X. U(C,X) is a subset of X such that U(C,X) =  {x| x is contained in some element of C}.

#This was copied from the file Countable Sets, which we needed for 2_22.

Definition. Let E be a nonempty  set such that for every element x of E x is a real number.
min(E) is an element of E such that for every element x of E min(E) =< x.

Axiom fin. Let E be a nonempty finite set such that for every element x of E x is a real number.
There exists an element x of E such that x = min(E).
#In the previous def and axiom we had to change the < for a =< and specify that E has to be nonempty.
#otherwise it yields a contradiction.
Axiom. Let X be a metric space. Let p be an element of X such that p is limit point of X in X.
Let r be a positive real number. Neigh(p,r,X) is nonempty.

Axiom. Let X be a metric space. Let p be an element of X. Let r,s be positive real numbers
such that r <= s. Neigh(p,r,X) is a subset of Neigh(p,s,X).

Axiom subfin. Let X be a finite set. Let Y be a subset of X. Y is finite. 

#The way we defined finiteness it would be really hard to prove this. It is simple enough to leave as an axiom.

Axiom 2_20. Let X be a metric space. Let p be an element of X such that p is limit point of X in X.
Let r be a positive real number. Neigh(p,r,X) is infinite.

Axiom 2_23. Let X be a metric space. Let Y be a subset of X. Y is open in X iff Compl(Y,X) is closed in X.

Axiom. Let X be a metric space. Let Y be a subset of X. Compl(Y,X) is a subset of X.

Axiom. Let X be a metric space. Let Y be a subset of X. Compl(Compl(Y,X),X) = Y.

Axiom 2_23_b. Let X be a metric space. Let Y be a subset of X. Y is closed in X iff Compl(Y,X) is open in X.

#2_24 requires MyChap2.

Definition 2_26_a. Let X be a metric space. Let Y be a subset of X. lim(Y,X) = {p | (p is an element of X 
such that p is limit point of Y in X)}.

Definition 2_26_b. Let X be a metric space. Let Y be a subset of X. cl(Y,X) = {p | (p is an element of Y) 
or (p is an element of lim(Y,X))}.

Axiom 2_27_a. Let X be a metric space. Let Y be a subset of X. cl(Y,X) is closed in X.


Axiom 2_27_b. Let X be a metric space. Let Y be a subset of X. Y = cl(Y,X) iff Y is closed in X.


Axiom 2_27_c. Let X be a metric space. Let Y be a subset of X. Let F be a subset of X such that 
(F is closed in X) and (Y is a subset of F). cl(Y,X) is a subset of F.


