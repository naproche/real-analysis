
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

Proposition 2_16. Let X be a metric space. Let Y be a subset of X. Then Y is a metric space.

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

Theorem 2_19. Let X be a metric space. Let r be a positive real number. Let p be an element of X. Neigh(p,r,X)
is open in X. 

Proof. Let us prove that every element of Neigh(p,r,X) is interior point of Neigh(p,r,X) in X.
Let q be an element of Neigh(p,r,X). Let us prove that q is interior point of Neigh(p,r,X) in X.
Then d(p,q) < r. r-d(p,q) is a positive real number.
Let us prove that every element of Neigh(q,r-d(p,q),X) is an element of Neigh(p,r,X).
Let s be an element of Neigh(q,r-d(p,q),X). Then d(q,s) < r-d(p,q).
We have d(p,s) <= d(p,q) + d(q,s). d(q,s) < r-d(p,q). d(p,q)+d(q,s) < d(p,q) + (r-d(p,q)).
d(p,q) + (r - d(p,q)) = r. Thus d(p,s) < r. 
Thus s is an element of Neigh(p,r,X). End.
Thus Neigh(q,r-d(p,q),X) is a subset of Neigh(p,r,X). 
Hence q is interior point of Neigh(p,r,X) in X. End. End.
Thus Neigh(p,r,X) is open in X. qed.

Definition.A natural number is an integer k such that k=0 or 0<k .
Definition. Let x and y be real numbers. x =< y iff x=y or x<y.
Let n denote a natural number.

Signature.Let x be a real number. abs(x) is a real number.
Axiom. Let x be a positive real number. abs(x) = x.
Axiom. abs(0)=0.
Axiom. Let x be a negative real number. abs(x)=-x.
Lemma. For every real number x 0=<abs(x).

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

#This was copied from the file Countable Sets, which we needed for 2_22.

Definition. Let E be a nonempty  set such that for every element x of E x is a real number.
min(E) is an element of E such that for every element x of E min(E) =< x.

Axiom fin. Let E be a nonempty finite set such that for every element x of E x is a real number.
There exists an element x of E such that x = min(E).
#In the previous def and axiom we had to change the < for a =< and specify that E has to be nonempty.
#otherwise it yields a contradiction.
Lemma. Let X be a metric space. Let p be an element of X such that p is limit point of X in X.
Let r be a positive real number. Neigh(p,r,X) is nonempty.

Lemma. Let X be a metric space. Let p be an element of X. Let r,s be positive real numbers
such that r <= s. Neigh(p,r,X) is a subset of Neigh(p,s,X).

Axiom subfin. Let X be a finite set. Let Y be a subset of X. Y is finite. 

#The way we defined finiteness it would be really hard to prove this. It is simple enough to leave as an axiom.

Theorem 2_20. Let X be a metric space. Let p be an element of X such that p is limit point of X in X.
Let r be a positive real number. Neigh(p,r,X) is infinite.

Proof. 
Assume the contrary. 
Take a natural number m such that Fin(m) is bigger than Neigh(p,r,X).
Take a map f such that Dom(f) = Fin(m) and f is surjective onto Neigh(p,r,X). 
Define E ={d(p,f(k)) | (k is an element of Fin(m)) and (f(k) != p)}. 
  Let us prove that every element x of E is a positive real number.
  Let x be an element of E. 
  Take an element k of Fin(m) such that x = d(p,f(k)) and f(k) != p.
  p != f(k). 
  f(k) is an element of X. 
  (By 2_15)  d(p,f(k)) > 0. Hence x > 0.
  End. 
Define F={d(p,f(k)) | k is an element of Fin(m)}.
Define g(k) = d(p,f(k)) for k in Fin(m).
 g is a map. 
g is surjective onto F. 
Thus F is finite. 
E is a subset of F.  
(By subfin) E is finite.
E is nonempty.
For every element x of E x is a real number. There exists an element d of E such that
d = min(E). 
Then min(E) is a positive real number.
Let us prove that for every element z of Neigh(p,min(E),X) z = p. 
   Let z be an element of Neigh(p,min(E),X). d(p,z) < min(E). 
   Suppose z != p. min(E) <= r. 
   Thus z is an element of Neigh(p,r,X). 
   Take a natural number l such that (l < m) and (f(l)=z).
   d(p,z)=d(p,f(l)) and f(l) != p. Thus d(p,z) is an element of E.
   d(p,z) < min(E). Contradiction. 
   End.
Let us prove that p is not limit point of X in X.
  Assume p is limit point of X in X. min(E) is a positive real number. For every element z
  of Neigh(p,min(E),X) z = p. Contradiction.
   End.
Contradiction.
 qed.

#This proof needs revision. The essence is there.

#So does 2_22.

Theorem 2_23. Let X be a metric space. Let Y be a subset of X. Y is open in X iff Compl(Y,X) is closed in X.

Proof. Let us prove that if (Y is open in X) then (Compl(Y,X) is closed in X). Proof. 
Suppose Y is open in X. Let p be an element of X such that p is limit point of Compl(Y,X) in X. 
For every positive real number r there exists an element q of Neigh(p,r,X) such that 
q is an element of Compl(Y,X). Thus p is not interior point of Y in X. Y is open in X. 
Hence p is not an element of Y. Thus p is an element of Compl(Y,X).
End.
Let us prove that if (Compl(Y,X) is closed in X) then (Y is open in X). Proof.
Suppose Compl(Y,X) is closed in X. Let us show that every element of Y is interior point of Y in X.
Proof. Let p be an element of Y. Thus p is not an element of Compl(Y,X).
Compl(Y,X) is closed in X. Hence p is not limit point of Compl(Y,X) in X. Take
a positive real number r such that (for every element q of Neigh(p,r,X) q is not an element of Compl(Y,X)).
Thus Neigh(p,r,X) is a subset of Y. Hence p is interior point of Y in X. End. Thus Y is open in X.
End.
qed.

Lemma. Let X be a metric space. Let Y be a subset of X. Compl(Y,X) is a subset of X.

Lemma. Let X be a metric space. Let Y be a subset of X. Compl(Compl(Y,X),X) = Y.

Corollary 2_23_b. Let X be a metric space. Let Y be a subset of X. Y is closed in X iff Compl(Y,X) is open in X.
Proof. (By 2_23) Compl(Y,X) is open in X iff Compl(Compl(Y,X),X) is closed in X. Compl(Compl(Y,X),X)=Y.
Thus Y is closed in X iff Compl(Y,X) is open in X.  qed.

#2_24 requires MyChap2.

Definition 2_26_a. Let X be a metric space. Let Y be a subset of X. lim(Y,X) = {p | (p is an element of X 
such that p is limit point of Y in X)}.

Definition 2_26_b. Let X be a metric space. Let Y be a subset of X. cl(Y,X) = {p | (p is an element of Y) 
or (p is an element of lim(Y,X))}.

Theorem 2_27_a. Let X be a metric space. Let Y be a subset of X. cl(Y,X) is closed in X.
Proof. Let us prove that Compl(cl(Y,X),X) is open in X. Let p be an element of Compl(cl(Y,X),X). 
Thus p is not an element of cl(Y,X). Thus p is not an element of Y
and p is not an element of lim(Y,X). Take a positive real number r such that (for every element q 
of Neigh(p,r,X) q is not an element of Y). Hence Neigh(p,r,X) is a subset of Compl(Y,X).
Let us prove that Neigh(p,r,X) is a subset of Compl(cl(Y,X),X). 
Let s be an element of Neigh(p,r,X). Assume s is an element of lim(Y,X). Take a positive real number
t such that Neigh(s,t,X) is a subset of Neigh(p,r,X). Then there exists an element c of X such that c is an element of
lim(Y,X) and c is an element of Neigh(p,r,X). Contradiction. Hence Neigh(p,r,X) is a subset of Compl(cl(Y,X),X). End.
Hence p is interior point of Compl(cl(Y,X),X) in X.
End. (By 2_23_b) cl(Y,X) is closed in X.
qed.

Theorem 2_27_b. Let X be a metric space. Let Y be a subset of X. Y = cl(Y,X) iff Y is closed in X.
Proof. Let us prove that if (Y=cl(Y,X)) then Y is closed in X. Proof. Suppose Y = cl(Y,X).
(By 2_23_a) cl(Y,X) is closed in X. Thus Y is closed in X.
End.
Let us prove that if Y is closed in X then Y = cl(Y,X). Proof. Suppose Y is closed in X. Then lim(Y,X) 
is a subset of Y. Thus Y = cl(Y,X).
End.
qed.

Theorem 2_27_c. Let X be a metric space. Let Y be a subset of X. Let F be a subset of X such that 
(F is closed in X) and (Y is a subset of F). cl(Y,X) is a subset of F.
Proof. F is closed in X. Thus lim(F,X) is a subset of F. Y is a subset of F. Hence lim(Y,X) is a subset
of F. Thus cl(Y,X) is a subset of F. qed.

