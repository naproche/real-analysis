Definition. The empty set is the set that has no elements.

Let A, B stand for sets. Let x is in A denote x is an element of A.

Definition.  A is nonempty iff A has an element.

Definition. A subset of B is a set A such that every element of A 
is an element of B.

Definition. A proper subset of B is a subset A of B such that there is
an element of B that  is not in A.

Lemma. Let A be a set. A is a subset of A.

Lemma. Let A be a set. A is not a proper subset of A.

Proof. Let us prove by contradiction that A is not a proper subset 
of A. Proof. Suppose there is an element of A that is not in A. Contradiction. End. qed.

Lemma. Let A and B be sets. If A is a subset of B and B is a subset of A 
then A=B.

Signature. Let x, w be elements. x < w is an relation.

Definition. Let E be a set. E is totally
ordered iff (for every element x of E  not x < x) and 
(for all element x,y of E x < y or y < x or x=y) and 
(for every elements x, y, z of E if x < y and y < z then x < z).

Lemma. Let E be a totally ordered set. Let a,b,c,d be elements of E.
Suppose a < b and b < c and c < d. a < d.

Proof. a < b, b < c. Then a < c. a < c and c < d. Then a < d. qed.

Lemma. Let E be a totally ordered set. Let F be a subset of E. Then 
F is totally ordered.

Let x <= y stand for x < y or x = y.
Let x < y stand for y < x.
Let x >= y stand for y <= x.

Definition. Let E be a totally ordered set. Let F be a subset of E.
Let s be an element of E. s is upper bound of F on E iff (for every element f
of F f <= s).

Definition. Let E be a totally ordered set. Let F be a subset of E.
F is bounded above on E iff (there exists an element s of E such that s is
upper bound of F on E).

Definition. Let E be a totally ordered set. Let F be a subset of E.
Let s be an element of E. s is lower bound of F on E iff (for every element f
of F f >= s).

Definition. Let E be a totally ordered set. Let F be a subset of E.
F is bounded below on E iff (there exists an element s of E such that s is
lower bound of F on E).

Definition. Let E be a totally ordered set. Let F be a subset of E. 
Let s be an element of E. s is supremum of F on E iff (s is upper bound of F 
on E) and (for every element t of E such that (t is upper bound of F on E) 
s <= t ).

Definition. Let E be a totally ordered set. Let F be a subset of E. 
Let s be an element of E. s is infimum of F on E iff (s is lower bound of F
on E) and (for every element t of E such that 
(t is lower bound of F on E) s >= t ).

Definition. Let E be a totally ordered set. E has least upper bound
property iff (for every subset F of E such that (F is bounded above on E) 
there is an element s of E such that (s is supremum of F on E)).

Axiom. Let E be a totally ordered set such that E has least upper bound
property. Let B be a subset of E such that (B is nonempty) and (B is
bounded below on E). Let L be the subset of B such that (every element in 
in L is an element e of E such that e is lower bound of B on E) and
(every element e of E such that e is lower bound of B on E is an element
in L). Then there is an element e of E such that (e is supremum of L on E) and
(e is infimum of B on E).





