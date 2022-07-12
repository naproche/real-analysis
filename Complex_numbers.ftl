[prove off ][read real-analysis/numbers.ftl] [prove on]

Signature 1_23. An extended real number is a mathematical object.

Definition 1_23_1. Real+ is the collection of extended real numbers.

Axiom 1_23_2. Let x be a real number. x is an extended real number.

Signature 1_23_3. \inf is an extended real number.
Signature 1_23_4. \neginf is an extended real number.

Signature 1_23_5. Let x,y be elements. x << y is a relation.

Definition 1_6_Ext. Let E be a set. E is totally
ordered iff (for every element x of E  not x << x) and 
(for all element x,y of E x << y or y << x or x=y) and 
(for all elements x, y, z of E if (x << y and y << z) then x << z).

Let x >> y stand for y << x.
Let x <<= y stand for x << y or x = y.
Let x >>= y stand for y << x or x = y.

Axiom 1_23_6. Let x,y be real numbers. x >> y iff x > y.
Axiom 1_23_7. Let x,y be real numbers. x << y iff x < y.
Axiom 1_23_8. Let x,y be real numbers. x <<= y iff x <= y.
Axiom 1_23_9. Let x,y be real numbers. x >>= y iff x >= y.

Axiom 1_23_i. Let x be an extended real number. \inf >> x.
Axiom 1_23_ii. Let x be an extended real number. (\neginf) << x.

Definition 1_7_Ext. Let E be a subset of Real+. An ext upper bound of E is an extended real number b such that
for all elements x of E x<<=b.
Definition 1_7b_Ext. Let E be a subset of Real+. An ext lower bound of E is an extended real number b such that
for all elements x of E b<<=x.

Definition 1_7a_Ext. Let E be a subset of Real+. E is ext bounded above iff E has an ext upper bound.
Definition 1_7c_Ext. Let E be a subset of Real+. E is ext bounded below iff E has an ext lower bound.


Definition 1_8_Ext. Let E be a subset of Real+. An ext least upper bound of E is an extended real number a such that
(a is an ext upper bound of E) and (for all extended real numbers x if x<<a then x is not an ext upper bound of E).
Definition 1_8a_Ext. Let E be a subset of Real+. Let E be ext bounded below. An ext greatest lower bound of E is a
extended real number a such that (a is an ext lower bound of E) and (for all extended real numbers x if x>>a then
x is not an ext lower bound of E).

Proposition. Let E be a subset of Real+. \inf is an ext upper bound of E.
Proposition. Let E be a subset of Real+. \neginf is an ext lower bound of E.


Axiom 1_9_Ext. Let E be a subset of Real+. Assume that E is nonempty. If E is ext bounded above then E has an ext least upper bound.
Axiom.  Let E be a subset of Real+. Assume that E is nonempty. If E is ext bounded below then E has an ext greatest lower bound.

Proposition 1_23_10. Let E be a nonempty subset of Real+. E has an ext least upper bound.
Proposition 1_23_10_1. Let E be a nonempty subset of Real+. E has an ext greatest lower bound.

Signature. Let x,y be extended real numbers. x++y is an extended real number.
Signature. Let x,y be extended real numbers. x**y is an extended real number.
Signature. Let x,y be extended real numbers. x over y is an extended real number.
Signature. Let x be an extended real number. neg(x) is an extended real number.

Definition. Let x be an extended real number. x is finite iff x is a real number.

Axiom. Let x be a finite extended real number. neg(x) = -x.
Axiom. Let x,y be finite extended real numbers. x++y = x+y.
Axiom. Let x,y be finite extended real numbers. Let y != 0.  x over y = x//y.
Axiom. neg(\inf) = \neginf.
Axiom. neg(\neginf) = \inf.

Let x minus y stand for x ++ neg(y).

Axiom 1_23_a_1. Let x be a finite extended real number. x ++ \inf = \inf.
Axiom 1_23_a_2. Let x be a finite extended real number. x minus \inf = \neginf.
Axiom 1_23_a_3. Let x be a finite extended real number. x over \inf = x over \neginf = 0.
Axiom 1_23_b_1. Let x be a positive finite extended real number. x ** \inf = \inf.
Axiom 1_23_b_2. Let x be a positive finite extended real number. x ** \neginf = \neginf.
Axiom 1_23_c_1. Let x be a negative finite extended real number. x ** \inf = \neginf.
Axiom 1_23_c_2. Let x be a negative finite extended real number. x ** \neginf = \inf.
