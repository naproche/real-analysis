[prove off ][read real-analysis/numbers.ftl] [prove on ]

Signature. A complex number is a mathematical object.

Definition. Complex is the collection of complex numbers.

Signature. Let x and y be complex numbers. x++y is a complex number.

Signature. Let x and y be complex numbers. x**y is a complex number.

Signature. Let x be a complex number. Re(x) is a real number.
Signature. Let x be a complex number. Im(x) is a real number.
Signature. Let x be a complex number. Let a,b be real numbers. x == (a,b) is an atom.

Axiom. Let x be a complex number. x == (Re(x), Im(x)).

Axiom. Let a,b be real numbers. Let x be a complex number.
If x == (a,b) then Re(x) = a, Im(x) = b.

Axiom. Let a,b,c,d be real numbers.
Let x,y be complex numbers such that x == (a,b) and  y == (c,d).
x++y == (a+b, c+d).

Axiom. Let a,b,c,d be real numbers.
Let x,y be complex numbers such that x == (a,b) and  y == (c,d).
x ** y == ((a*c)-(b*d), (a*d)+(b*c)).

Axiom. Let a,b,c,d be real numbers. Let x be a complex number. 
If x == (a,b) and x == (c,d) then a=c and b=d. 

Axiom. Let a,b be real numbers. Let x,y be complex numbers. 
If x == (a,b) and y == (a,b) then x = y.

#Signature. i is a complex number such that i == (0,1).

Signature. One is a complex number such that One == (1,0).
Signature. Zero is a complex number such that Zero == (0,0).

Theorem. Re(Zero) = 0.
Theorem. Im(Zero) = 0.
Theorem. Re(One) = 1.
Theorem. Re(One) = 0.


#Signature. Let x be a real number. c(x) is a complex number such that c(x) == (x,0).


Theorem. One == (1,0).
Theorem. Zero == (0,0).
Theorem. Contradiction.

#Theorem. Let x,y be complex numbers. x++y = y++x.