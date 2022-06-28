[read real-analysis/vocabulary.ftl]
[read vocabulary.ftl]
[read macros.ftl]

### Classes

Let S,T denote classes.
Let j denote an object.

Axiom. Every set is a class.

Axiom. Every element of every class is an object.

Let j \in S stand for j is an element of S.
Let j \notin S stand for j is not an element of S.

Definition DefSub.
A subclass of S is a class T such that every x \in T belongs to S.

Let T \subseteq S stand for T is a subclass of S.

Axiom Extensionality. If S is a subclass of T and
T is a subclass of S then S = T.

### Maps

Let f denote a map.

Definition.
Assume M is a subclass of the domain of f. f[M] = { f(x) | x \in M }.

Definition.
The union of S and T is {x | x \in S or x \in T}.
Let S \cup T stand for the union of S and T.

Definition 1_3. S is nonempty iff S has an element.

# The Real Field

Signature. A real number is a mathematical object.

Definition. Real is the collection of real numbers.

Axiom. Real is a set.

Let x, y, z denote real numbers.

Signature 1_12_A1. x + y is a real number.
Let the sum of x and y stand for x + y.

Signature 1_12_M1. x * y is a real number.
Let the product of x and y denote x * y.

Signature 1_5. x < y is an atom.
Let x > y stand for y < x.
Let x<=y stand for x < y or x = y.
Let x>=y stand for y<=x.

Axiom 1_5_i. not x < x.

Axiom 1_5_ii. If x < y and y < z then x < z.

Axiom 1_5_iii. If x != y then x < y or y < x.

Axiom 1_12_A2. x+y=y+x.
Axiom 1_12_A3. (x+y)+z=x+(y+z).
Signature 1_12_A4. 0 is a real number such that for every real number x x+0=x.

Signature 1_12_A5. -x is a real number such that x + (-x)=0.

Axiom 1_12_M2. x*y=y*x.
Axiom 1_12_M3. (x*y)*z=x*(y*z).
Signature 1_12_M4. 1 is a real number such that 1 != 0 and for every real number x 1*x = x.
Signature 1_12_M5. Assume x!=0. 1/x is a real number such that x * 1/x = 1.

Axiom 1_12_D. x*(y+z)= (x*y)+(x*z).
Axiom 1_14_a. If x+y = x+z then y = z.

Axiom 1_15_a. If x!=0 and x*y=x*z then y=z.

Axiom 1_16_c. -x*y=-(x*y)=x*(-y).

Let x-y stand for x+(-y).

Let x//y stand for x * 1/y.

# The Real Ordered Field

Axiom 1_17_i. If x<y then x+z<y+z.
Axiom 1_17_ii. If x>0 and y>0 then x*y>0.
Definition. x is positive iff x>0.
Definition. x is negative iff x<0.

Axiom 1_18_b. If z>0 and x<y then x*z < y*z.

Axiom. x<y iff -x>-y.

Axiom 1_18_c. If z<0 and x<y then x*z > y*z.

Axiom 1_18_ee. Assume 0 < x < y. Then 1/y < 1/x.

# Upper and lower bounds

Let E denote a subclass of Real.

Definition 1_7. An upper bound of E is a real number b such that
for all elements x of E x<=b.
Definition 1_7a. E is bounded above iff E has an upper bound.
Definition 1_7b. A lower bound of E is a real number b such that for
all elements x of E x>=b.
Definition 1_7c. E is bounded below iff E has a lower bound.

Definition 1_8. A least upper bound of E is a real number a such that
a is an upper bound of E and for all x if x<a then x is not an upper bound of E.
Definition 1_8a. A greatest lower bound of E is a real number a such that
a is a lower bound of E and for all x if x>a then x is not a lower bound of E.

Axiom 1_19. Assume that E is nonempty and bounded above.
Then E has a least upper bound.

Definition. E^- = {-x in Real | x \in E}.

Axiom 1_11. Assume that E is nonempty and bounded below.
Then E has a greatest lower bound.

# Integers

Signature. An integer is a real number.
Let a, b stand for integers.

Definition. Integer is the collection of integers.

# Integer is a discrete subring of Real.

Axiom. a+b, a*b are integers.
Axiom. 0, -1, 1 are integers.
Axiom. There is no integer a such that 0<a<1.

Axiom Archimedes. There is an integer m such that m <= x < m+1.

# The Natural numbers.

Definition. Natural is the collection of positive integers.

Let m, n stand for positive integers.

Axiom Induction_Theorem.
Assume A \subseteq Natural and 1 \in A and for all n \in A n+1 \in A.
Then A = Natural.

# Archimedian properties.

Axiom 1_20_a. Let x > 0. 
Then there is a positive integer n such that n * x > y.
