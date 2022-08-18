[synonym field/-s]
[prove off][read real-analysis/numbers.ftl][read real-analysis/Countable_sets.ftl][prove on]

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
such that q is an element of Y).

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

Proof. Let us prove that every element of Neigh(p,r,X) is interior point of Neigh(p,r,X) in X. Proof.
Let q be an element of Neigh(p,r,X). Let us prove that q is interior point of Neigh(p,r,X) in X.
Proof. 
Then d(p,q) < r. r-d(p,q) is a positive real number.
Let us prove that every element of Neigh(q,r-d(p,q),X) is an element of Neigh(p,r,X).
Proof.
Let s be an element of Neigh(q,r-d(p,q),X). Then d(q,s) < r-d(p,q).
We have d(p,s) <= d(p,q) + d(q,s). d(q,s) < r-d(p,q). Then d(p,q)+d(q,s) < d(p,q) + (r-d(p,q)).
Thus d(p,s) < r.
Thus s is an element of Neigh(p,r,X). End.
Thus Neigh(q,r-d(p,q),X) is a subset of Neigh(p,r,X). 
Hence q is interior point of Neigh(p,r,X) in X. End. End.
Thus Neigh(p,r,X) is open in X. qed.

Theorem 2_20. Let X be a metric space. Let p be an element of X such that p is limit point of X in X.
Let r be a positive real number. Neigh(p,r,X) is infinite.

Proof. Suppose Neigh(p,r,X) is finite. 
Contradiction. qed.

#2_20 requires MyChap2 (infinite) which I still haven't been able to read here.

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