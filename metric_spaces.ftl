[synonym field/-s]
[prove off] [read numbers.ftl][prove on]

Signature. Let p,q be elements. d(p,q) is a real number.

Signature. A metric space is a set.

Axiom 2_15_a1. Let X be a metric space. Let p be an element of X. d(p,p)=0.
Axiom 2_15_a2. Let X be a metric space. Let p and q be elements of X. d(p,q) >= 0.
Axiom 2_15_b. Let X be a metric space. Let p and q be elements of X. d(p,q)=d(q,p).
Axiom 2_15_c.  Let X be a metric space. Let p, q and r be elements of X. d(p,q) <= d(p,r) + d(r,q).

Axiom 2_16. Let X be a metric space. Let Y be a subset of X. Y is a metric space.

#This holds as the axioms are still satisfied. I do not know if we can ask Naproche to prove this as 
#we have not specified what a metric space actually is, just stated what properties should it have.

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

Proof. Let q be an element of Neigh(p,r,X). Let us prove that q is interior point of Neigh(p,r,X) in X.
Proof. 
Then d(p,q) < r. r-d(p,q) is a positive real number. Let s be
an element of X such that s is an element of Neigh(q,r-d(p,q),X). Then d(q,s) < r-d(p,q).
We have d(p,s) <= d(p,q) + d(q,s). d(q,s) < r-d(p,q). Then d(p,q)+d(q,s) < d(p,q) + r-d(p,q).
Thus d(p,s) < r.
Thus s is an element of Neigh(p,r,X). Thus Neigh(q,r-d(p,q),X) is a subset of Neigh(p,r,X). 
Hence q is interior point of Neigh(p,r,X) in X. End.
Then Neigh(p,r,X) is open in X.
qed.

#This is a theorem we should later prove.

#2_20 requires MyChap2 (infinite) which I still haven't been able to read here.

#So does 2_22.

Theorem 2_23. Let X be a metric space. Let Y be a subset of X. Y is open in X iff Compl(Y,X) is closed in X.

#This is a theorem we should later prove.

#2_24 requires MyChap2.

Definition 2_26_a. Let X be a metric space. Let Y be a subset of X. lim(Y,X)={p | (p is an element of X 
such that p is limit point of Y in X)}.

Definition 2_26_b. Let X be a metric space. Let Y be a subset of X. cl(Y,X) = {p | (p is an element of Y) 
or (p is an element of lim(Y,X))}.

Lemma. Let X be a metric space. Let Y be a subset of X. cl(Y,X) is a subset of X.

Axiom 2_27_a. Let X be a metric space. Let Y be a subset of X. cl(Y,X) is closed in X.
Axiom 2_27_b. Let X be a metric space. Let Y be a subset of X. Y = cl(Y,X) iff Y is closed in X.
Axiom 2_27_c. Let X be a metric space. Let Y be a subset of X. Let F be a subset of X such that 
(F is closed in X) and (Y is a subset of F). cl(Y,X) is a subset of F.

#This should be theorems.

