[prove off ][read numbers.ftl] [prove on ]

Signature. A complex number is a mathematical object.

Definition. Complex is the collection of complex numbers.

Signature 1_24_2a. Let x and y be complex numbers. x++y is a complex number.

Signature 1_24_3a. Let x and y be complex numbers. x**y is a complex number.

Signature 1_30_1. Let x be a complex number. Re(x) is a real number.
Signature 1_30_2. Let x be a complex number. Im(x) is a real number.
Signature 1_24_1a. Let x be a complex number. Let a,b be real numbers. x == (a,b) is a relation.

Axiom 1_30_0. Let x be a complex number. x == (Re(x), Im(x)).

Axiom 1_24_2b. Let a,b,c,d be real numbers.
Let x,y be complex numbers such that x == (a,b) and  y == (c,d).
x++y == (a+c, b+d).

Axiom 1_24_2bb.
Let x,y be complex numbers. x++y == (Re(x)+Re(y), Im(x)+Im(y)).

Axiom 1_24_3b. Let a,b,c,d be real numbers.
Let x,y be complex numbers such that x == (a,b) and  y == (c,d).
x ** y == ((a*c)-(b*d), (a*d)+(b*c)).

Axiom 1_24_3bb.
Let x,y be complex numbers. x**y == ((Re(x)*Re(y))-(Im(x)*Im(y)), (Re(x)*Im(y))+(Im(x)*Re(y))).

Axiom 1_24_1b. Let a,b,c,d be real numbers. Let x be a complex number. 
If x == (a,b) and x == (c,d) then a=c and b=d. 

Axiom 1_24_1c. Let a,b be real numbers. Let x,y be complex numbers. 
If x == (a,b) and y == (a,b) then x = y.

#Axiom 1_26. Let x be a real number. x is a complex number such that x == (x,0).

Signature 1_27. i is a complex number such that i == (0,1).

#Theorem 1_25_A1. 0 == (0,0).
Signature 1_25_A1. Zero is a complex number such that Zero == (0,0).

Axiom 1_25_A2. Let x,y be complex numbers. x++y = y++x.
Axiom 1_25_A3. Let x,y,z be complex numbers.(x++y)++z = x++(y++z). 
Theorem 1_25_A4. Let x be a complex number. x ++ Zero = x.
Proof.
(x ++ Zero) == (Re(x) + Re(Zero),Im(x) + Im(Zero)) (by 1_24_2bb).
Qed.
Signature 1_12_A5. Let x be a complex number. _x is a complex number such that x ++ (_x) = Zero.

#Theorem 1_25_M1. 1 == (1,0).

Signature 1_25_M1. One is a complex number such that One == (1,0).
Axiom 1_25_M2. Let x,y be complex numbers. x**y = y**x.
Axiom 1_25_M3. Let x,y,z be complex numbers.(x**y)**z = x**(y**z).
Theorem 1_25_M4. Let x be a complex number. x ** One = x.
Proof.
(x ** One) == ((Re(x) * Re(One))-(Im(x)*Im(One)),(Re(x)*Im(One))+(Im(x)*Re(One))) (by 1_24_3bb).
Qed.
Signature 1_25_M5. Let x be a complex number. \x is a complex number such that x ** \x = One.

Axiom 1_25_D1. Let x,y,z be complex numbers. x**(y++z) = (x**y)++(x**z).
Axiom 1_25_D2. Let x,y,z be complex numbers. (x++y)**z = (x**z)++(y**z).

Theorem 1_26_a. Let a and b be real numbers. Let x and y be complex numbers such that
x == (a,0) and y ==(b,0). Then x++y == (a+b,0).

Proof. x++y == (a + b, 0 + 0). qed.

Theorem 1_26_b. Let a and b be real numbers. Let x and y be complex numbers such that
x == (a,0) and y ==(b,0). Then x**y == (a*b,0).

Theorem 1_28. i**i = _One.

Theorem 1_29. Let a,b be real numbers. Let x,y be complex numbers such that x == (a,0) and y == (b,0). x ++ (y**i) == (a,b).

Signature. Let x be a complex number. conj(x) is a complex number.

Definition 1_30. Let x be a complex number. conj(x) == (Re(x),-Im(x)).

Signature. Let x be a complex number. neg(x) is a complex number.

Definition. Let x be a complex number. neg(x) == (-Re(x),-Im(x)).

Definition. Let x be a complex number. x is complexreal iff Im(x) = 0.

Axiom 1_31_a. Let z,w be complex numbers. conj(z++w) = conj(z) ++ conj(w).
Axiom 1_31_b. Let z,w be complex numbers. conj(z**w) = conj(z) ** conj(w).
Axiom 1_31_c1. Let z be a complex number. z ++ (conj(z)) == (Re(z)+Re(z),0).
Axiom 1_31_c2. Let z be a complex number. z ++ (neg(conj(z))) == (0,Im(z)+Im(z)).
Axiom 1_31_d1. Let z be a complex number. z ** (conj(z)) is complexreal.
Axiom 1_31_d2. Let z be a complex number such that Re(z) is not 0. Re(z ** (conj(z))) 
is positive.
