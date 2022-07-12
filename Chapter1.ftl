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

Definition 1_6. Let E be a set. E is totally
ordered iff (for every element x of E  not x < x) and 
(for all element x,y of E x < y or y < x or x=y) and 
(for every elements x, y, z of E if x < y and y < z then x < z).

Lemma. Let E be a totally ordered set. Let a,b,c,d be elements of E.
Suppose a < b and b < c and c < d. a < d.

Proof. a < b, b < c. Then a < c. a < c and c < d. Then a < d. qed.

Lemma. Let E be a totally ordered set. Let F be a subset of E. Then 
F is totally ordered.

Let x <= y stand for x < y or x = y.
Let x > y stand for y < x.
Let x >= y stand for y <= x.

Definition 1_7a. Let E be a totally ordered set. Let F be a subset of E.
Let s be an element of E. s is upper bound of F on E iff (for every element f
of F f <= s).

Definition 1_7b. Let E be a totally ordered set. Let F be a subset of E.
F is bounded above on E iff (there exists an element s of E such that s is
upper bound of F on E).

Definition 1_7c. Let E be a totally ordered set. Let F be a subset of E.
Let s be an element of E. s is lower bound of F on E iff (for every element f
of F f >= s).

Definition 1_7d. Let E be a totally ordered set. Let F be a subset of E.
F is bounded below on E iff (there exists an element s of E such that s is
lower bound of F on E).

Definition 1_8a. Let E be a totally ordered set. Let F be a subset of E. 
Let s be an element of E. s is supremum of F on E iff (s is upper bound of F 
on E) and (for every element t of E such that (t is upper bound of F on E) 
s <= t ).

Definition 1_8b. Let E be a totally ordered set. Let F be a subset of E. 
Let s be an element of E. s is infimum of F on E iff (s is lower bound of F
on E) and (for every element t of E such that 
(t is lower bound of F on E) s >= t ).

Definition 1_10. Let E be a totally ordered set. E has least upper bound
property iff (for every subset F of E such that (F is bounded above on E) 
there is an element s of E such that (s is supremum of F on E)).

Axiom 1_11. Let E be a totally ordered set such that E has least upper bound
property. Let B be a subset of E such that (B is nonempty) and (B is
bounded below on E). Let L be the subset of B such that (every element in 
in L is an element e of E such that e is lower bound of B on E) and
(every element e of E such that e is lower bound of B on E is an element
in L). Then there is an element e of E such that (e is supremum of L on E) and
(e is infimum of B on E).

Signature. A field is a nonempty set.

Signature. Let x and y be elements. x + y is an element.
Signature. Let x and y be elements. x*y is an element.

Proposition. Let F be a field. Let x be an element of F. Then x is an element.

Axiom 1_12_A1. Let F be a field. Let x, y be elements of F. x + y is an element of F.
Axiom 1_12_A2. Let F be a field. Let x and y be elements of F. x+y = y+x.
Axiom 1_12_A3. Let F be a field. Let x,y and z be elements of F. (x+y)+z=x+(y+z).
Signature 1_12_A4_1. 0 is a element.
Axiom 1_12_A4_2. Let F be a field. 0 is in F.
Axiom 1_12_A4_3. Let F be a field. x + 0  = x for every element x of F.
Signature 1_12_A5. Let F be a field. Let x be a element of F. neg(x,F) is a element of F such that x + neg(x,F)= 0.

Axiom 1_12_M1.  Let F be a field. Let x and y be elements of F. x*y is in F.
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
Proposition 1_16_b.  Let F be a field. Let x,y be elements of F. If x!=0 and y!=0 then x*y!=0.
Proposition 1_16_c.  Let F be a field. Let x,y be elements of F. (x*y) + (neg(x,F)*y) = 0.
Proof. (x*y)+(neg(x,F)*y) = (x+ (neg(x,F)))*y =0*y = 0. Qed.
#Axiom. Let F be a field. Let x,y be elements of F. (neg(x,F)*y) = neg(x*y,F).
#Proof.  (x*y) + (neg(x,F)*y) = 0 (by 1_16_c). Let z =  (neg(x,F)*y). Let w = x*y. 
#w + z = 0. Thus z = neg(w,F). Thus neg(x,F)*y = neg(x*y,F). Qed.
Proposition.  Let F be a field. Let x be an element of F. neg(x,F)= neg(1,F) * x.
#Proposition 1_16_d.  Let F be a field. Let x,y be elements of F. neg(x,F)*neg(y,F)= x*y.
#Proof. neg(x,F)*neg(y,F)=neg(x*neg(y,F),F)=neg(neg(y,F)*x,F)=neg(neg(y*x,F),F)= y*x = x*y. Qed.

Signature. An ordered field is a set.

Axiom 1_17_0. Let F be an ordered field. Then F is totally ordered.
Axiom 1_17_1. Let F be an ordered field. Then F is a field.
Axiom 1_17_i. Let F be an ordered field. Let x,y,z be elements of F. If y < z then x + y < x + z.
Axiom 1_17_ii. Let F be an ordered field. Let x,y,z be elements of F. If x > 0 and y > 0 then x*y > 0.

Definition. Let F be an ordered field. Let x be an element of F. x is positive in F iff x > 0.
Definition. Let F be an ordered field. Let x be an element of F. x is negative in F iff x < 0.
Definition. Let F be an ordered field. Let x be an element of F. x is nonzero in F iff x != 0.
#Proposition.  Let F be an ordered field. Let x be an element of F. If x is nonzero then x is positive in F or x is negative in F.
Proposition. Let F be an ordered field. Let x be an element of F. x is positive in F or x is negative in F or x=0.

#Axiom. Let F be an ordered field. Let x be an element of F. Then (x is positive in F) or (x is negative in F) or (x = 0).
#Proposition 1_18_a. Let F be an ordered field. Let x be an element of F. x>0 iff neg(x,F)<0.
#Proof. Let us prove that (if x > 0 then neg(x,F) < 0).
# Proof. Suppose x > 0. Then 0 = neg(x,F) + x > neg(x,F) + 0 = neg(x,F). Qed.
#Let us prove that (if neg(x,F) <  0 then x > 0). 
#Proof. Suppose neg(x,F) < 0. Then 0 = neg(x,F) + x < 0 + x = x. Qed. 
#Qed.

Proposition 1_18_a_1. Let F be an ordered field. Let x be an element of F. If x > 0 then neg(x,F)<0.
Proof. Suppose x > 0. Then 0 = neg(x,F) + x > neg(x,F) + 0 = neg(x,F). Qed. 


Proposition 1_18_a_2. Let F be an ordered field. Let x be an element of F. If neg(x,F)<0 then x > 0.
Proof. Suppose neg(x,F) < 0. Then 0 = neg(x,F) + x < 0 + x = x. Qed.

Proposition 1_18_a. Let F be an ordered field. Let x be an element of F. x>0 iff neg(x,F)<0.
 
Axiom 1_18_b. Let F be an ordered field. Let x,y,z be elements of F. If x > 0 and y < z then x*y< x*z.
#Proof. Suppose x>0 and y<z.
#z+neg(y,F) > y + neg(y,F)=0.
#x*(z+neg(y,F)) > 0.
#x*z=(x*(z+neg(y,F)))+ (x*y). 
#(x * (z + neg(y,F))) + (x * y)  > 0 + (x * y) (by 1_17_i).
#0+(x*y)= x*y.
#Qed.

Proposition 1_18_bb.  Let F be an ordered field. Let x,y,z be elements of F. If x>0 and y<z then y*x<z*x.


Proposition 1_18_d. Let F be an ordered field. Let x be an element of F. If x is nonzero in F then x*x > 0.
Proof. Case x > 0. x*x > x*0 = 0. End.
Case x < 0. Then neg(x,F) > 0. End.
Qed.
 

#Proposition 1_18_dd. 1>0.

#Proposition.  Let F be an ordered field. Let x,y be elements of F. x<y iff neg(x,F)>neg(y,F).
#Proof.
#x<y iff x+neg(y,F)<0.
#x+neg(y,F)<0 iff (neg(y,F))+x<0.
#(neg(y,F))+x<0 iff (neg(y,F))+(neg(neg(x,F),F)) <0.
#(neg(y,F))+(neg(neg(x,F),F))<0 iff (neg(y,F))+neg(neg(x,F),F)<0.
#(neg(y,F))+neg(neg(x,F),F)<0 iff neg(y,F)<neg(x,F).
#Qed.

#Proposition 1_18_c. Let F be an ordered field. Let x,y,z be elements of F. If x<0 and y<z then x*y>x*z.
#Proof. Let x<0 and y<z.
#neg(x,F) > 0.
#(neg(x,F))*y < (neg(x,F))*z (by 1_18_b).
#neg(x*y,F) < neg(x*z,F).
#Qed.

#Proposition 1_18_cc.  Let F be an ordered field. Let x,y,z be elements of F. If x<0 and y<z then y*x>z*x.

#Proposition. Let F be an ordered field. Let x be an element of F. x+1>x.
#Proposition. Let F be an ordered field. Let x be an element of F. x + neg(1,F) < x.

#Proposition 1_18_e. Let F be an ordered field. Let y be an element of F. If 0<y then 0< inv(y,F).

#Proposition 1_18_ee. Let F be an ordered field. Let x,y be elements of F. Assume 0 < x < y. Then inv(y,F) < inv(x,F).
#Proof.
#Case inv(x,F) < inv(y,F). 
#Then 1 = x*(inv(x,F))=(inv(x,F))*x < (inv(x,F))*y = y*(inv(x,F)) < y * (inv(y,F))=1.
#Contradiction. End.
#Case inv(x,F)=inv(y,F).
#Then 1 = x*(inv(x,F)) < y*(inv(y,F))=1.
#Contradiction. End.
#Hence inv(y,F) < inv(x,F) (by 1_5_i).
#Qed.
