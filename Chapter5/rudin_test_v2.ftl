[prove off]
[read preliminaries.ftl]
[read real-analysis/numbers.ftl]
[prove on]

Let f,g denote functions.

Let o denote an object.
Let x,y,z denote real numbers.
Let S,S' denote sets.

Definition PSubset.
  A proper subset of S is a set S'
  such that S' is subset of S and
  there exists o such that o \in S
  and o does not belong to S'.

#real valued functions
Let f is real valued stand for
Dom(f) is nonempty subset of Real and
Ran(f) is nonempty subset of Real. #this is provable
#nonemptiness avoid trivialites.

Definition.
  (x | y) is a subset of Real such that for every real number i
  i belongs to (x | y) iff x < i < y.
Let S is open interval stand for S = (x|y) for some nonequal real numbers x,y
such that x < y.
Lemma. 
  Let S be open interval. 
  S is nonempty subset of Real.

Definition.
  [x | y] is a subset of Real such that for every real number i
  i belongs to [x | y] iff x <= i <= y.
Let S is closed interval stand for S = [x|y] for some nonequal real numbers x,y
such that x < y.
Lemma.
  Let S be closed interval. 
  S is nonempty subset of Real and
  S is bounded above and
  S is bounded below.

Definition.
  Let S be closed interval.
  The interior of S is a subset S' of S such that 
  S' is open interval and there exists no subset S'' of S
  such that S' is proper subset of S'' and S'' is open interval.
#would be nice to say "... the greatest open interval in S.".

Lemma.
  Let x < y.
  (x|y) is the interior of [x|y]. 
Proof.
  (x|y) is subset of [x|y].
  (x|y) is open interval.
  Let us show that there exists no subset S of [x|y] such that
  (x|y) is proper subset of S and S is open interval.
    Assume the contrary.
    Take subset S of [x|y] such that (x|y) is proper subset of S and S is open interval.
    Take real numbers x',y' such that S = (x'|y'). 
    Then (x > x' and y' >= y) or (x >= x' or y < y'). Indeed (x|y) is proper subset of S.
    x <= x' and y' <= y. 
    Proof by contradiction.
      Let us show that if x' < x then contradiction.
        Assume x' < x.
        Take z such that x' < z < x.
        z belongs to S and z does not belong to [x|y].
      end.
      Let us show that if y' > y then contradiction.
        Assume y' > y.
        Take z such that y' > z > y.
        z belongs to S and z does not belong to [x|y].
      end.
    end.    
  end.
end.

#Lemma. Contradiction.

# "... on ..." causes ambiguity whith l.70 of preliminaries.
Let f is defined in S stand for S is a subset of Dom(f). 

Definition DefCons. 
    S u {o} = { y | y \in S or y = o}.
Axiom. S u {x} is a set.
Lemma.
  Let S be nonempty set.
  For every o \in S S u {o} = S.
 
Definition DefDiff.
    S/{o} = {y | y \in S and y != o}.

Lemma. #TEST
  Assume f is real valued and defined in (x|y) for some nonequal x,y such that x < y.
  Then for every x' \in Dom(f) f(x') is a real number.

#absolute value of real numbers
Signature. |x| is an object.
Axiom.
  If x is positive then |x| = x.
Axiom.
  If x is negative then |x| = -x.
Axiom.
  If x = 0 then |x| = 0.

Lemma. #TEST
  x is positive or x is negative or x = 0.

Lemma. #TEST
  |x| is a positive real number or |x| = 0.

Lemma. #TEST
  x <= |x| and -x <= |x|.

Lemma. #TEST
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
  Case x + y is positive. 
    Then |x + y| = x + y <= |x| + |y|. 
  end.
  Case x + y is negative. 
    Then |x + y| = -(x + y) =  (-1) * (x + y) = ((-1)*x) + ((-1)*y) = (-x) + (-y) <= |x| + |y|.
  end.
  Case  x + y = 0. 
    Then |x + y| = 0 <= |x| <= |x| + |y|. 
  end.
QED.

Lemma.
  If x < y then there exists z such that x < z < y. 

Lemma. 
  Let S be open interval and s' belongs to S.
  S/{s'} is nonempty subset of Real.
Proof.
  Take nonequal x,y such that S=(x|y) and x<y.
  Take z such that x<z<y.
  z belongs to S.
  Case s' < z. Obvious.
  Case s' = z.
    Take real number z' such that x < z' < s'.
    z' belongs to S/{z}. Indeed z' belongs to S.
  end.
  Case s' > z. Obvious.
end.

Lemma. 
  Let S be closed interval and s' belongs to S.
  S/{s'} is nonempty subset of Real.

#Lemma. Contradiction.

#being "real valued" is too general and encompasses cases which are
#not important for the present formalization i.e a punctuated function
#or when Dom(f) is a singleton. These cases mean that we cannot approach 
#a given point in the domain with arbitrary degree of closeness. Therefore
#the concept of limit is somewhat vague and those cases should be ruled out.

#real numbers
Lemma.
  Let d1, d2 be positive real numbers.
  Then there exists a positive real number d
  such that d < d1 and d < d2.
Proof.
  Take positive integer n such that
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
        (y1 + ((-f(z)) + f(z))) - y2 = (y1 + (-f(z))) + (f(z) - y2).
        Then |(y1 + ((-f(z)) + f(z))) - y2| = |(y1 + (-f(z))) + (f(z) - y2)|.
        (y1 + (-f(z))) + (f(z) - y2) = (y1 - f(z)) + (f(z) - y2).
        Then |(y1 + (-f(z))) + (f(z) - y2)| = |(y1 - f(z)) + (f(z) - y2)|.
        |(y1 - f(z)) + (f(z) - y2)| <= |y1 - f(z)| + |f(z) -  y2| (By TriangleIneq).
        |y1 -  f(z)| + |f(z) - y2| = |f(z) - y1| + |f(z) - y2|.
      End.
      Let us show that  |f(z) - y1| + |f(z) -  y2| <= e + e.
        |f(z) - y1| <= (e).
        Hence |f(z) - y1| + |f(z) -  y2| <= (e) + |f(z) -  y2|.
        |f(z) - y2| <= (e).
        Hence e + |f(z) -  y2| <= (e) + (e).
      End.      
      If |y1 - y2| <= (|f(z) - y1| + |f(z) -  y2|)
      and (|f(z) - y1| + |f(z) -  y2|) <= e + e then 
      |y1 - y2| <=  e + e.  
      Proof.
        For every real number x',y',z'
        if x' <= y' and y' <= z' then x' <= z'.
        |y1 - y2| is a real number.
        (|f(z) - y1| + |f(z) -  y2|) is a real number.
        e + e is a real number.
        If |y1 - y2| <= (|f(z) - y1| )
        and (|f(z) - y1| ) <= e + e then 
        |y1 - y2| <=  e + e.  
        Proof.
          For every real number x',y',z'
          if x' <= y' and y' <= z' then x' <= z'.
          |y1 - y2| is a real number.
          (|f(z) - y1| ) is a real number.
          e + e is a real number.
        end.
      end.
      |y1 - y2| <= (|f(z) - y1| + |f(z) -  y2|)
      and (|f(z) - y1| + |f(z) -  y2|) <= e + e.
    End.  
    e + e = (1+1)*e.
  end.
  Therefore the thesis (by Fredy). Indeed (1+1) is a positive real number.
QED.

#Lemma. Contradiction.

Lemma.
  Let x,y be real numbers such that x < y.
  Let f be real valued and defined in [x|y].
  Let x' belongs to Dom(f).
  (Dom(f))/{x'} is a nonempty subset of Real.

Signature. The quotient difference of f at z is a function.
Axiom.
  Let S be closed interval and z belong to S.
  Let S' be the interior of S.
  Let f be real valued and defined in S.
  The quotient difference of f at z is a function g such that 
  S'/{z} is a subset of Dom(g) and z \notin Dom(g) and
  for every t \in S'/{z} g(t) = (f(t) - f(z))*(1/(t-z)).
  
Lemma.
  Let f be real valued and defined in [x|y].
  For every z \in [x|y] 
  there exists the quotient difference of f at z.
 
Lemma.
  Contradiction.