[synonym field/-s]

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
 
Signature. A field is a nonempty set.

Signature. Let x and y be elements. x + y is an element.
Signature. Let x and y be elements. x*y is an element.

Axiom 1_12_A1. Let F be a field. Let x, y be elements of F. Then x + y is an element of F.
Axiom 1_12_A2. Let F be a field. Let x and y be elements of F. x+y = y+x.
Axiom 1_12_A3. Let F be a field. Let x,y and z be elements of F. (x+y)+z=x+(y+z).
Signature 1_12_A4_1. 0 is a element.
Axiom 1_12_A4_2. Let F be a field. 0 is in F.
Axiom 1_12_A4_3. Let F be a field. x + 0  = x for every element x of F.
Signature 1_12_A5. Let F be a field. Let x be a element of F. neg(x,F) is a element of F such that x + neg(x,F)= 0.

Axiom 1_12_M1.  Let F be a field. Let x and y be elements of F. If x is in F and y is in F then x*y is in F.
Axiom 1_12_M2.  Let F be a field. Let x and y be elements of F. x*y=y*x.
Axiom 1_12_M3.  Let F be a field. Let x,y and z be elements of F. (x*y)*z=x*(y*z).
Signature 1_12_A4_1.  1 is a element.
Axiom 1_12_A4_2.  Let F be a field. 1 is in F.
Axiom 1_12_A4_3.  Let F be a field. x * 1 = x for every element x of F.
Signature 1_12_M5. Let F be a field. Let x be a element of F. Assume x != 0. inv(x,F) is a element of F such that x * inv(x,F) = 1.

Axiom 1_12_D.  Let F be a field.  Let x,y and z be elements of F. x*(y+z)= (x*y)+(x*z).
Proposition Dist1.  Let F be a field.  Let x,y and z be elements of F. (y*x)+(z*x)=(y+z)*x.
Proposition 1_14_a.  Let F be a field. Let x,y and z be elements of F. If x+y = x+z then y = z.
Proof. Assume x+y=x+z. Then y = (neg(x,F)+x)+y=neg(x,F)+(x+y)=neg(x,F)+(x+z)=(neg(x,F)+x)+z=z. Qed.

Proposition 1_14_b.  Let F be a field. Let x,y be elements of F. If x+y=x then y=0.
Proposition 1_14_c. Let F be a field. Let x,y be elements of F. If x+y=0 then y=neg(x,F).
Proposition 1_14_d. Let F be a field. Let x be a element of F. neg(neg(x,F),F)=x.
Proposition 1_15_a. Let F be a field.  Let x,y,z be elements of F. If x!=0 and x*y=x*z then y=z.
Proof. Let x!=0 and x*y=x*z. y=1*y=(inv(x,F) * x)* y = inv(x,F)*(x*y)=inv(x,F)*(x*z)=(inv(x,F)*x)*z= 1* z=z. Qed.
Proposition 1_15_b.  Let F be a field. Let x,y be elements of F. If x!=0 and x*y=x then y=1.
Proposition 1_15_c.  Let F be a field. Let x,y be elements of F. If x!=0 and x*y=1 then y=inv(x,F).
Proposition 1_15_d.  Let F be a field. Let x be a element of F. If x!=0 then inv(inv(x,F),F)= x.

Proposition 1_16_a.  Let F be a field.  Let x be a element of F. 0*x=0.
Proposition 1_16_b.  Let F be a field. Let x,y be element of F. If x!=0 and y!=0 then x*y!=0.
Proposition.  Let F be a field. Let x be an element of F. neg(x,F)*1 = neg(x*1,F).
Proposition 1_16_c.  Let F be a field. Let x,y be elements of F. (neg(x,F) * y) = neg(x*y,F).
Proof. (x*y)+(neg(x,F)*y) = (x+ (neg(x,F)))*y =0*y = 0. Qed.
Proposition 1_16_d.  Let F be a field. Let x,y be elements of F. neg(x,F)*neg(y,F)= x*y.
Proof. neg(x,F)*neg(y,F)=neg(x*neg(y,F),F)=neg(neg(y,F)*x,F)=neg(neg(y*x,F),F)= y*x = x*y. Qed.
