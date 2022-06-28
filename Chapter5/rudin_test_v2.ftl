[prove off]
[read preliminaries.ftl]
[read real-analysis/numbers.ftl]
[prove on]

Let f denote a function.

Let x,y,z denote real numbers.

#real valued functions
Let f is real valued stand for
Dom(f) is subset of Real and
Ran(f) is subset of Real.

Lemma.
  Assume f is real valued.
  Then for every x \in Dom(f) f(x) is a real number.

#absolute value of real numbers
Signature. |x| is an object.
Axiom.
  If x is positive then |x| = x.
Axiom.
  If x is negative then |x| = -x.
Axiom.
  If x = 0 then |x| = 0.

Lemma.
  x is positive or x is negative or x = 0.

Lemma.
  |x| is a positive real number or |x| = 0.

Lemma.
  x <= |x| and -x <= |x|.

Lemma.
  |x| = |-x|.

Lemma.
  |x - y| = |y - x|.
Proof.
  |x - y| = |-(x - y)| = |(-x) + y| = |y - x|.
QED.

Lemma DoubleLeq.
  Let x1, x2, y1, y2 be real numbers.
  Assume x1 <= y1 and x2 <= y2.
  Then x1 + x2 <= y1 + y2.
Proof.
  x1 <= y1.
  x1 + x2 <= y1 + x2 <= y1 + y2.
QED.

Lemma TriangleIneq.
  |x + y| <= |x| + |y|.
Proof.
  x + y <= |x| + |y|.
  x + y is positive or x + y is negative or x + y = 0.
  If x + y is positive
  then |x + y| = x + y <= |x| + |y|.
  If x + y is negative
  then |x + y| = -(x + y) =  (-1) * (x + y) = ((-1)*x) + ((-1)*y) = (-x) + (-y) <= |x| + |y|.
  If x + y = 0
  then |x + y| = 0 <= |x| <= |x| + |y|.
QED.


#real numbers
Lemma.
  Let d1, d2 be positive real numbers.
  Then there exists a positive real number d
  such that d < d1 and d < d2.
Proof.
  There exists a positive integer n such that
  n > 1/d1 and n > 1/d2.
  Let n be a positive integer such that
  n > 1/d1 and n > 1/d2.
  Then 1/n < d1 and 1/n < d2.
QED.

Lemma LeqTransivity.
  Assume x <= y and y <= z.
  Then x <= z.


#limit of a real valued function at x
Definition Limit.
  Let f be real valued.
  y is limit of f at x iff
    for every positive real number e
    there exists a positive real number d
    such that for every real number z
    if z \in Dom(f) and 0 < |z - x| < d
    then |f(z) - y| < e.

Definition.
  (x | y) is a set such that for every real number i
  i belongs to (x | y) iff x < i < y.

Lemma.
  for every positive real number x
  There exists positive real number y such that
  0 < y < x.

Lemma Fredy.
  Let a be a positive real number.
  Assume that for every positive real number e  
  |x-y| <= a*e. 
  Then x = y.
Proof.
  Assume |x-y| != 0. 
  Then |x-y|>0.
  1/a * |x-y| is a positive real number.
  Take positive real number e such that
  e < 1/a * |x-y|.
  a*e < (a * 1/a) *|x-y| = |x-y|.
  Then |x-y| <= a*e < |x-y|.
end.

Lemma.
  Let f be real valued.
  Let y1, y2 be real numbers.
  Assume y1, y2 is limit of f at x and
  for every positive real number d
  there exists z \in Dom(f) such that
  0 < |z - x| < d.
  Then y1 = y2.
Proof.
  Let us show that for every positive real number e |y1 - y2| <= (1+1)*e.
  Let e be a positive real number.
  Take positive real number d1 such that  for every real number z
     if z \in Dom(f) and 0 < |z - x| < d1
    then |f(z) - y1| < (e) (by Limit).
  Take positive real number d2
  such that for every real number z
     if z \in Dom(f) and 0 < |z - x| < d2
    then |f(z) - y2| < (e) (by Limit).
  Take a positive real number d such that
  d < d1 and d < d2.
  Take element z such that
  z belongs to Dom(f) and
  0 < |z - x| < d.

  Then |f(z) - y1| <= (e).
  Then |f(z) - y2| <= (e).
  
  Let us show that |y1 - y2| <=  e + e.
    Let us show that |y1 - y2| <= |f(z) - y1| + |f(z) -  y2|.
      |y1 - y2| = |(y1 + ((-f(z)) + f(z))) - y2|.
      |(y1 + ((-f(z)) + f(z))) - y2| = |(y1 + (-f(z))) + (f(z) - y2)| = |(y1 - f(z)) + (f(z) - y2)|.
      |(y1 - f(z)) + (f(z) - y2)| <= |y1 - f(z)| + |f(z) -  y2| (By TriangleIneq).
      |y1 -  f(z)| + |f(z) - y2| = |f(z) - y1| + |f(z) - y2|.
    End.
    Let us show that  |f(z) - y1| + |f(z) -  y2| <= e + e.
      |f(z) - y1| <= (e).
      Hence |f(z) - y1| + |f(z) -  y2| <= (e) + |f(z) -  y2|.
      |f(z) - y2| <= (e).
      Hence e + |f(z) -  y2| <= (e) + (e).
    End.
    |y1 - y2| <= (|f(z) - y1| + |f(z) -  y2|)
    and (|f(z) - y1| + |f(z) -  y2|) <= e + e.
  End.  
  e + e = (1+1)*e.
  end.
  Therefore the thesis (by Fredy). Indeed (1+1) is a positive real number.
QED.
