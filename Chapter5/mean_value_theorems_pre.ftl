[prove off]
[check off]
[read preliminaries.ftl]
[read real-analysis/numbers.ftl]
[timelimit 20]

#SETS
Definition SetMinus.
  Let S be a set.
  Let o be an object.
  S\\{o} = {x | x \in S and x != o}.


# MAPS
Let f denote a map.

Definition Codomain.
  Let S be a class.
  f is into S iff for any x \in Dom(f) we have f(x) \in S.

Definition Image.
  Suppose M \subseteq Dom(f).
  f[M] = { f(j) | j \in M }.

Definition RealMap.
  A real map is a map f such that
    Dom(f) \subseteq Real and f is into Real.

Definition IdentityMapOf.
  Let S be a set.
  The identity map of S is a map f such that
  Dom(f) = S and for any x \in S f(x) = x.

Definition IdentityMap.
  An identity map is a real map f such that
  f is the identity map of Dom(f).

Definition ConstantMapWithValue.
  Let c be a real number.
  A constant map with value c is a real map f such that
  for any t \in Dom(f) f(t) = c.

Definition ConstantMap.
  A constant map is a real map f such that
  there exists a real number c such that
  for any t \in Dom(f) f(t) = c.

Lemma RealMapsEvaluateToRealNumbers.
  Let f be a real map.
  Let t be an element of Dom(f).
  Then f(t) is a real number.


# MAP OPERATIONS
Definition Composition.
  Let f, g be maps. Suppose f is into Dom(g).
  g \circ f is a map h such that Dom(h) = Dom(f) and
  for any x \in Dom(f) we have g(f(x)) = h(x).

Definition Addition.
  Let f, g be maps into Real. Suppose Dom(f) = Dom(g).
  f ++ g is a map h such that Dom(h) = Dom(f) and
  for any x \in Dom(h) we have h(x) = f(x) + g(x).

Definition Multiplication.
  Let f, g be maps into Real. Suppose Dom(f) = Dom(g).
  f ** g is a map h such that Dom(h) = Dom(f) and
  for any x \in Dom(h) we have h(x) = f(x) * g(x).

Definition Scaling.
  Let f be a map into Real.
  Let c be a real number.
  c~f is a map h such that Dom(h) = Dom(f) and
  for any t \in Dom(h) h(t) = c*f(t).

Definition Restriction.
  Let f be a map.
  A restriction of f is a map g such that
    Dom(g) is a subset of Dom(f)
    and for any x \in Dom(g) g(x) = f(x).

Lemma AdditionOfRealMaps.
  Let f,g be real map.
  Suppose Dom(f) = Dom(g).
  Then f++g is a real map that is defined on Dom(f).

Lemma MultiplicationOfRealMaps.
  Let f,g be real map.
  Suppose Dom(f) = Dom(g).
  Then f**g is a real map that is defined on Dom(f).

Lemma ScalingOfRealMap.
  Let f be a real map.
  Let c be a real number.
  Then c~f is a real map that is defined on Dom(f).

Lemma RestrictionOfRealMap.
  Let f be a real map.
  Let g be a restriction of f.
  Then g is a real map.


# INTERVALS
Definition OpenInterval.
  Let x,y be real numbers.
  (x|y) is a subset of Real such that
  for every real number i
  i belongs to (x|y) iff x < i < y.

Definition ClosedInterval.
  Let x,y be real numbers.
  [x|y] is a subset of Real such that
  for every real number i
  i belongs to [x|y] iff x <= i <= y.


# COMPACTNESS
Signature.
  Let S be a subset of Real.
  S is compact is an atom.

Axiom Compactness.
  Let x,y be real numbers.
  [x|y] is compact.


# DISTANCE OPERATOR
Let x,y denote real numbers.
Signature Distance. d(x,y) is a real number.
Axiom d1. d(x,y) = 0 iff x = y.
Axiom d2. d(x,y) = d(y,x).
Axiom d3. Let z be a real number. d(x,z)<=d(x,y)+d(y,z).
Axiom d4. Let c be a positive real number. d(x,y) < c iff y-c < x < y+c.


# LIMIT POINTS
Let E denote a subclass of Real.

Definition LimitPoint.
  A limit point of E is a real number p such that
    for any positive real number eps
    there exists e \in E such that 0 < d(e,p) < eps.

Definition SubsetOfLimitPoints.
  A subset of limit points of E is a subset P of E such that
    for any p \in P p is a limit point of E.

Lemma LimitPointAxiom1.
  Let z be an element of [x|y].
  Let t be an element of [x|y].
  Then t is a limit point of [x|y] and
       t is a limit point of [x|y]\\{z} and
       t is a limit point of (x|y) and
       t is a limit point of (x|y)\\{z}.
#! Proof!

Lemma LimitPointAxiom2.
  Let p be a limit point of E.
  Let e be an element of E.
  Then p is a limit point of E\\{e}.
#! Proof!

Lemma LimitPointOfSupset.
  Let F be a subclass of Real.
  Let E be a subclass of F.
  Assume p is a limit point of E.
  Then p is a limit point of F.
#! Proof!

Lemma.
  Let x,y be real numbers.
  (x|y) is a subset of limit points of [x|y].
#! Proof!

Lemma.
  Let x,y be real numbers.
  (x|y) is a subset of limit points of (x|y).
#! Proof


# LIMIT
Definition LimitWrtAnd.
  Let f be a real map.
  Let p be a limit point of Dom(f).
  Let q be a real number.
  Let eps, del be positive real numbers.
  q is limit of f at p wrt eps and del iff
    for any t \in Dom(f) if 0<d(t,p)<del then d(f(t),q)<eps.

Definition LimitWrt.
  Let f be a real map.
  Let p be a limit point of Dom(f).
  Let q be a real number.
  Let eps be a positive real number.
  q is limit of f at p wrt eps iff there exists a positive real number del such that
    q is limit of f at p wrt eps and del.

Signature Limit.
  Let f be a real map.
  Let p be a limit point of Dom(f).
  lim(f,p) is an object.
Axiom LimitAxiom.
  Let f be a real map.
  Let p be a limit point of Dom(f).
  Let q be a real number.
  lim(f,p) = q iff for any positive real number eps
    q is limit of f at p wrt eps.

Let the limit of f at p stand for lim(f,p).

Definition LimitExists.
  Let f be a real map.
  Let p be a limit point of Dom(f).
  lim(f,p) exists iff lim(f,p) is a real number.

Theorem 4_4a.
  Let f, g be real map such that Dom(f) = Dom(g).
  Let p be a limit point of Dom(f).
  If lim(f,p) exists and lim(g,p) exists then lim(f++g,p) = lim(f,p) + lim(g,p).

Theorem 4_4b.
  Let f, g be real map such that Dom(f) = Dom(g).
  Let p be a limit point of Dom(f).
  If lim(f,p) exists and lim(g,p) exists then lim(f**g,p) = lim(f,p) * lim(g,p).


# CONTINUITY
Let f denote a real map.

Definition ContinuousAtWrtAnd.
  Let p be an element of Dom(f).
  Let eps be a positive real number.
  Let del be a positive real number.
  f is continuous at p wrt eps and del iff
    for any t \in Dom(f) if 0<d(t,p)<del then d(f(t),f(p))<eps.
Definition ContinuousAtWrt.
  Let p be an element of Dom(f).
  Let eps be a positive real number.
  f is continuous at p wrt eps iff
    there exists positive real number del such that f is continuous at p wrt eps and del.
Definition ContinuousAt.
  Let p be an element of Dom(f).
  f is continuous at p iff for any positive real number eps
    f is continuous at p wrt eps.

Definition Continuous.
  f is continuous iff for any p \in Dom(f) f is continuous at p.

Theorem 4_6.
  Let f be a real map.
  Let p be an element of Dom(f) that is a limit point of Dom(f).
  f is continuous at p iff lim(f,p) = f(p).

Theorem 4_9a. 
  Let f,g be real map such that Dom(f) = Dom(g).
  Let p \in Dom(f).
  Suppose f is continuous at p and g is continuous at p.
  Then f++g is continuous at p.

Theorem 4_9b. 
  Let f,g be real map such that Dom(f) = Dom(g).
  Let p \in Dom(f).
  Suppose f is continuous at p and g is continuous at p.
  Then f**g is continuous at p.

Lemma ContinuityOfRestriction.
  Let f be a real map.
  Let g be a restriction of f.
  Let p be an element of Dom(g).
  If f is continuous at p then g is continuous at p.
#! Proof

Theorem 4_16a.
  Suppose f is continuous and Dom(f) is nonempty and compact.
  Then there exists p \in Dom(f) such that
    for any t \in Dom(f) f(t) <= f(p).

Theorem 4_16b.
  Suppose f is continuous and Dom(f) is nonempty and compact.
  Then there exists p \in Dom(f) such that
    for any t \in Dom(f) f(t) >= f(p).


# DIFFERENCE QUOTIENT
Let f denote a real map.
Let p denote a real number.

Definition DifferenceQuotient.
  Let p be an element of Dom(f).
  DQ(f,p) is a map g such that
    Dom(g) = (Dom(f))\\{p} and
    for any t \in Dom(g) g(t) = (f(t)-f(p)) // (t-p).

Lemma DifferenceQuotientIsARealMap.
  Let p be an element of Dom(f).
  Then DQ(f,p) is a real map.


# DERIVATIVE
Let f denote a real map.

Signature Derivative.
  Let f be a real map.
  Let p be an element of Dom(f) that is a limit point of Dom(f).
  D(f,p) is an object.
Axiom DerivativeAxiom.
  Let f be a real map.
  Let p be an element of Dom(f) that is a limit point of Dom(f).
  Let q be a real number.
  D(f,p) = q iff lim(DQ(f,p),p) = q.

Definition Differentiable.
  Let p be an element of Dom(f) that is a limit point of Dom(f).
  f is differentiable at p iff D(f,p) is a real number.

Definition.
  Let P be a subset of limit points of Dom(f).
  f is differentiable on P iff
    for any p \in P f is differentiable at p.

Theorem 5_2.
  Let f be a real map.
  Let p be an element of Dom(f) that is a limit point of Dom(f).
  If f is differentiable at p then f is continuous at p.

Theorem 5_3a.
  Let f be a real map such that f is defined on [x|y].
  Let g be a real map such that g is defined on [x|y].
  Let p be an element of (x|y).
  Assume that f is differentiable at p.
  Assume that g is differentiable at p.
  Then f++g is differentiable at p and
  D(f++g,p) = D(f,p) + D(g,p).