# Importing Set-Theoretic Preliminaries

[timelimit 10]
[read real-analysis/vocabulary.ftl]
[read preliminaries.ftl]

Let A,B stand for sets.
Let x is in A denote x is an element of A.

Lemma. A = A.

Definition. Let B, C be classes.
The union of B and C is { x | x \in B or x \in C}.
Let B \cup C stand for the union of B and C.


Definition 1_3. A is nonempty iff A has an element.

# The Real Field

Signature. A real number is a mathematical object.

Definition. Real is the collection of real numbers.

Let x, y, z denote real numbers. 

Axiom. Real is a set.

Signature 1_12_A1. x + y is a real number.
Let the sum of x and y stand for x + y.

Signature 1_12_M1. x * y is a real number.
Let the product of x and y denote x * y.

Signature 1_5. x < y is an atom.
Let x > y stand for y < x.
Let x<=y stand for x < y or x = y.
Let x>=y stand for y<=x.

Axiom 1_5_i. (x < y and x != y and not y < x)
or (not x < y and x = y and not y < x)
or (not x < y and x != y and y < x).

Axiom 1_5_ii. If x < y and y < z then x < z.

Proposition. x <= y iff not x > y.

Axiom 1_12_A2. x+y=y+x.
Axiom 1_12_A3. (x+y)+z=x+(y+z).
Signature 1_12_A4. 0 is a real number such that for every real number x x+0=x.

Signature 1_12_A5. -x is a real number such that x + (-x)=0.

Axiom 1_12_M2. x*y=y*x.
Axiom 1_12_M3. (x*y)*z=x*(y*z).
Signature 1_12_M4. 1 is a real number such that 1 != 0 and for every real number x 1*x = x.
Signature 1_12_M5. Assume x!=0. 1/x is a real number such that x * 1/x = 1.

Axiom 1_12_D. x*(y+z)= (x*y)+(x*z).
Proposition Dist1. (y*x)+(z*x)=(y+z)*x.
Proposition 1_14_a. If x+y = x+z then y = z.
Proof. Assume x+y=x+z. Then y = (-x+x)+y=-x+(x+y)=-x+(x+z)=(-x+x)+z=z. Qed.

Proposition 1_14_b. If x+y=x then y=0.
Proposition 1_14_c. If x+y=0 then y=-x.
Proposition 1_14_d. -(-x)=x.
Proposition 1_15_a. If x!=0 and x*y=x*z then y=z.
Proof. Let x!=0 and x*y=x*z. y=1*y=(1/x * x)* y = 1/x*(x*y)=1/x*(x*z)=(1/x*x)*z= 1* z=z. Qed.
Proposition 1_15_b. If x!=0 and x*y=x then y=1.
Proposition 1_15_c. If x!=0 and x*y=1 then y=1/x.
Proposition 1_15_d. If x!=0 then 1/(1/x)= x.

Proposition 1_16_a. 0*x=0.
Proposition 1_16_b. If x!=0 and y!=0 then x*y!=0.
Proposition 1_16_c. -x*y=-(x*y).
Proof. (x*y)+(-x*y)= (x+ (-x))*y=0*y=0. Qed.
Proposition. -x=-1* x.
Proposition 1_16_d. -x*(-y)= x*y.
Proof. -x*(-y)=-(x*(-y))=-((-y)*x)=-(-(y*x))= y*x = x*y. Qed.

Let x-y stand for x+(-y).

Let x//y stand for x * 1/y.

# The Real Ordered Field

Axiom 1_17_i. If y<z then x+y<x+z and y+x < z+x.
Axiom 1_17_ii. If x>0 and y>0 then x*y>0.
Definition. x is positive iff x>0.
Definition. x is negative iff x<0.

Proposition 1_18_a. x>0 iff -x<0.
Proposition 1_18_b. If x>0 and y<z then x*y< x*z.
Proof. Let x>0 and y<z.
z-y > y-y=0.
x*(z-y) > 0.
x*z=(x*(z-y))+ (x*y).
(x * (z - y)) + (x * y)  > 0 + (x * y) (by 1_17_i).
0+(x*y)= x*y.
Qed.

Proposition 1_18_bb. If x>0 and y<z then y*x<z*x.
Proposition 1_18_d. If x !=0 then x*x>0.
Proof. Let x!=0.
Case x>0. Then thesis. End.
Case x<0. Then -x >0. End.
Qed.

Proposition 1_18_dd. 1>0.

Proposition. x<y iff -x>-y.
Proof.
x<y iff x-y<0.
x-y<0 iff (-y)+x<0.
(-y)+x<0 iff (-y)+(-(-x)) <0.
(-y)+(-(-x))<0 iff (-y)-(-x)<0.
(-y)-(-x)<0 iff -y<-x.
Qed.

Proposition 1_18_c. If x<0 and y<z then x*y>x*z.
Proof. Let x<0 and y<z.
-x > 0.
(-x)*y < (-x)*z (by 1_18_b).
-(x*y) < -(x*z).
Qed.

Proposition 1_18_cc. If x<0 and y<z then y*x>z*x.

Proposition. x+1>x.
Proposition. x-1<x.

Proposition 1_18_e. If 0<y then 0<(1/y).

Proposition 1_18_ee. Assume 0 < x < y. Then 1/y < 1/x.
Proof.
Case 1/x < 1/y. 
Then 1 = x*(1/x)=(1/x)*x < (1/x)*y = y*(1/x) < y * (1/y)=1.
Contradiction. End.
Case 1/x=1/y.
Then 1 = x*(1/x) < y*(1/y)=1.
Contradiction. End.
Hence 1/y< 1/x (by 1_5_i).
Qed.

# Upper and lower bounds

Let E denote a subset of Real.

Definition 1_7. An upper bound of E is a real number b such that
for all elements x of E x<=b.
Definition 1_7a. E is bounded above iff E has an upper bound.
Definition 1_7b. A lower bound of E is a real number b such that for
all elements x of E x>=b.
Definition 1_7c. E is bounded below iff E has a lower bound.

Definition 1_8. A least upper bound of E is a real number a such that
a is an upper bound of E and for all x if x<a then x is not an upper bound of E.
Definition 1_8a. Let E be bounded below. A greatest lower bound of E is a
real number a such that a is a lower bound of E and for all x if x>a then
x is not a lower bound of E.

Axiom 1_19. Assume that E is nonempty and bounded above. Then E has a least upper bound.

Definition. E^- = {-x in Real | x \in E}. 

Lemma. E^- is a subset of Real.

Lemma. x is an upper bound of E iff -x is a lower bound of E^-.

Theorem 1_11. Assume that E is a nonempty subset of Real
such that E is bounded below.
Then E has a greatest lower bound.
Proof.
Take a lower bound a of E.
-a is an upper bound of E^-.
Take a least upper bound b of E^-.
Let us show that -b is a greatest lower bound of E.
-b is a lower bound of E. 
Let us show that for every lower bound c of E we have c<=-b.
Let c be a lower bound of E.
Then -c is an upper bound of E^-.
End.
End.
Qed.

# The Rational Numbers

Signature 1_19a. A rational number is a real number.

Let p, q, r denote rational numbers.

Definition. Rational is the collection of rational numbers.

Theorem. Rational is a set.
Proof. Rational is a subset of Real. Qed.

# Theorem 1.19 of \cite{Rudin} states that $\mathbb{Q}$ is a 
# subfield of $\mathbb{R}$. We require this axiomatically.

Lemma. Rational \subseteq Real.

Axiom. p+q, p*q, 0, -p, 1 are rational numbers.
Axiom. Assume p!=0. 1/p is a rational number.

Axiom. There exists a subset A of Rational
such that A is bounded above and 
x is a least upper bound of A.

Theorem. Real = {x in Real | there exists A \subseteq Rational such that
A is bounded above and x is a least upper bound of A}.

# Integers

Signature. An integer is a rational number.
Let a, b, i stand for integers.

Definition. Integer is the collection of integers.

Theorem. Integer is a subset of Real.

# Integer is a discrete subring of Rational.

Axiom. a+b, a*b, 0, -1, 1 are integers.
Axiom. There is no integer a such that 0<a<1.
Axiom. There exist a and b such that a!=0 and p = b//a.

Theorem Archimedes1. Integer is not bounded above.
Proof. Assume the contrary.
Integer is nonempty. Indeed 0 is an integer.
Take a least upper bound b of Integer.
Let us show that b-1 is an upper bound of Integer.
Let us show that for every integer x we have x <= b-1.
Let x be an integer. 
x+1 \in Integer.
x+1 <= b.
x = (x+1)-1 <= b-1.
End.
End.
Qed.

Theorem. Integer is not bounded below.
Proof. Assume the contrary.
Take lower bound m of Integer.
Then -m is an upper bound of Integer. Contradiction.
Qed.

Theorem Archimedes2. Let x be a real number.
Then there is an integer a such that x<a.
Proof. Assume the contrary.
Then x is an upper bound of Integer. Contradiction.
Qed.

# The Natural numbers.

Definition. Natural is the collection of positive integers.

Let m, n stand for positive integers.

Lemma. Natural is a subset of Real.

Definition. {x}={y in Real | y=x }.

Lemma. Integer = (Natural^- \cup {0}) \cup Natural.

Theorem Induction_Theorem. Assume A \subseteq Natural and 1 \in A
and for all n \in A n+1 \in A.
Then A = Natural.
Proof.
Let us show that every element of Natural is an element of A.
  Let n \in Natural.
  Assume the contrary.
  Define F = {j | j\in Natural and j \notin A}.
  F is nonempty. F is bounded below.
  Take a greatest lower bound a of F.
  Let us show that a+1 is a lower bound of F.
    Let us show that for every element x of F we have a+1<=x.
    Let x \in F.  
    x-1 \in Integer.
    Case x-1 < 0. Then 0<x<1. Contradiction. End.
    Case x-1 = 0. Then x = 1 and 1 \notin A. Contradiction. End.
    Case x-1 > 0. Then x-1 \in Natural.
    x-1 \notin A. Indeed (x-1)+1 = x \notin A.
    x-1 \in F.
    a <= x-1.
    a+1 <= (x-1)+1=x.
    End.
    End.
  End.

  Then a+1 > a.
  Contradiction.
End.
Qed.


Lemma. There is an integer m such that m-1 <= x < m.

Proof. Assume the contrary.
Then for all m such that x >= m-1 we have x >= m.
Take an integer n such that n<x.
Define A={ i in Natural | n+(i-1) <= x}.

Let us show that A = Natural.
  A \subseteq Natural. 1 \in A.
  Let us show that for all i\in A i+1\in A.
    Let i\in A. Then 
    n+(i-1)=(n+i)-1 <= x and n+((i+1)-1) = n+i <= x.
  Then i+1 \in A. 
  End.
  Then A = Natural. # by Induction_Theorem.
End.

Let us show that x+1 is an upper bound of Integer.
Let us show that for every integer j we have j <= x+1.
Let j be an integer. 
Case j <= n. Trivial.
Then j>n. Take a positive integer i such that j=n+i.
i\in A.
Hence n+(i-1) <= x and j=n+i <= x+1.
End.
End.
Contradiction.
Qed.


# Archimedian properties.

Theorem 1_20_a. Let x>0. 
Then there is a positive integer n such that
n * x > y.
Proof.
Take an integer a such that a > y//x.
Take a positive integer n such that n > a.
n > y//x.
n*x > (y//x) * x = y.
Qed.

Theorem 1_20_b. Let x < y. Then there exists p \in Rational
such that x < p < y.
Proof. We have y-x > 0.
Take a positive integer n such that n*(y-x)>1 (by 1_20_a).
Take an integer m such that
m-1 <= n * x < m.
Then
n * x < m = (m-1)+1 <= (n*x)+1 < (n*x)+(n*(y-x)) = n*(x+(y-x)) = n*y.
n>0 and
x = (n*x)//n < m//n < (n*y)//n = y.
Choose p such that p = m//n. Then p \in Rational and x < p < y.
Qed. 
