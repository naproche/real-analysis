[prove off]
[check off]
[read preliminaries.ftl]
[read real-analysis/numbers.ftl]
[timelimit 20]

[prove on]
[check on]

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

Lemma.
  Let f be a real map.
  Let c be a real number.
  Then c~f is a real map.


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

Definition.
  A limit point of E is a real number p such that
    for any positive real number eps
    there exists e \in E such that d(e,p) < eps.

[prove off]
Lemma LimitPointAxiom1.
  Let z be an element of [x|y].
  Let t be an element of [x|y].
  Then t is a limit point of [x|y] and
       t is a limit point of [x|y]\\{z} and
       t is a limit point of (x|y) and
       t is a limit point of (x|y)\\{z}.
# Proof!

Lemma LimitPointAxiom2.
  Let p be a limit point of E.
  Let e be an element of E.
  Then p is a limit point of E\\{e}.
# Proof!

Lemma LimitPointOfSupset.
  Let F be a subclass of Real.
  Let E be a subclass of F.
  Assume p is a limit point of E.
  Then p is a limit point of F.
# Proof!
[prove on]


# LIMIT
Signature.
  Let f be a real map.
  lim(f,p) is an object.

Axiom LimitAxiom.
  Let f be a real map.
  Let p be a limit point of Dom(f).
  Let q be a real number.
  lim(f,p) = q iff for any positive real number eps
    there exists a positive real number del such that
    for any t \in Dom(f) if 0<d(t,p)<del then d(f(t),q)<eps.

[prove off]
Lemma ExistenceOfDel.
  Let f be a real map.
  Let p be a limit point of Dom(f).
  Let q be a real number such that lim(f,p) = q.
  Assume that eps is a positive real number.
  Then there exists a positive real number del such that
    for any t \in Dom(f) if 0<d(t,p)<del then d(f(t),q)<eps.
# Proof!
[prove on]

Lemma LimitOfConstantFunction.
  Let c be a real number.
  Let const be a real map such that
    for any t \in Dom(const) const(t) = c.
  Let p be a limit point of Dom(const).
  Then lim(const,p) = c.
Proof.
  Let us show that for any positive real number eps
  there exists a positive real number del such that
  for any t \in Dom(const) if 0<d(t,p)<del then d(const(t),c)<eps.
    Assume that eps is a positive real number.
    Let us show that for any t \in Dom(const) if 0<d(t,p)<1 then d(const(t),c)<eps.
      Assume t \in Dom(const) and 0<d(t,p)<1.
      Then d(const(t),c)=0. Indeed const(t) = c.
      Then d(const(t),c)<eps.
    End.
  End.
  lim(const,p) = c iff for any positive real number eps
    there exists a positive real number del such that
    for any t \in Dom(const) if 0<d(t,p)<del then d(const(t),c)<eps (by LimitAxiom).
  Indeed const is a real map and p is a limit point of Dom(const) and c is a real number.
  Therefore the thesis.
End.

[prove off]
Lemma LimitOfRestrictedFunction.
  Let f,g be real map such that Dom(g) is a subset of Dom(f).
  Let p be a limit point of Dom(g).
  Let q be a real number such that lim(f,p) = q.
  Assume that for any t \in Dom(g) g(t) = f(t).
  Then lim(g,p) = q.
Proof.
  Then p is a limit point of Dom(f) (by LimitPointOfSupset).
  Let us show that for any positive real number eps there exists
  a positive real number del such that
  for any  t \in Dom(g) if 0<d(t,p)<del then d(g(t),q)<eps.
    Assume that eps is a positive real number.
    There exists a positive real number del such that 
      for any t \in Dom(f) if 0<d(t,p)<del then d(f(t),q)<eps.
    Indeed q is a real number such that lim(f,p) = q.
    Take a positive real number del such that for any
      t \in Dom(f) if 0<d(t,p)<del then d(f(t),q)<eps.
    Let us show that for any t \in Dom(g) if 0<d(t,p)<del then d(g(t),q)<eps.
      Take t \in Dom(g).  
      Then t \in Dom(f). Indeed Dom(g) is a subset of Dom(f).
      Let us show that if 0<d(t,p)<del then d(g(t),q)<eps.
        Assume 0<d(t,p)<del.
        Then d(f(t),q)<eps.
        Then d(g(t),q)<eps. Indeed g(t) = f(t).
      End.
    End.
  End.
  Then lim(g,p) = q iff for any positive real number eps
    there exists a positive real number del such that
    for any t \in Dom(g) if 0<d(t,p)<del then d(g(t),q)<eps (by LimitAxiom).
  Therefore the thesis.
QED.
[prove on]


# CONTINUITY
Let f denote a real map.

Definition ContinuousAt.
  Let p be an element of Dom(f).
  f is continuous at p iff for any positive real number eps
    there exists positive real number del such that
    for any t \in Dom(f) if 0<d(t,p)<del then d(f(t),f(p))<eps.

Definition Continuous.
  f is continuous iff for any p \in Dom(f) f is continuous at p.

[prove off]
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

Lemma ContinuityOfScaledFunction.
  Let f be a real map.
  Let c be a real number.
  Let p be an element of Dom(f).
  Suppose that f is continuous at p.
  Then c~f is continuous at p.
# Proof!

Theorem 4_16a.
  Suppose f is continuous and Dom(f) is nonempty and compact.
  Then there exists p \in Dom(f) such that
    for any t \in Dom(f) f(t) <= f(p).

Theorem 4_16b.
  Suppose f is continuous and Dom(f) is nonempty and compact.
  Then there exists p \in Dom(f) such that
    for any t \in Dom(f) f(t) >= f(p).
[prove on]


# DIFFERENCE QUOTIENT
Let f denote a real map.
Let p denote a real number.

Definition DifferenceQuotient.
  Let p be an element of Dom(f).
  DQ(f,p) is a map g such that
    Dom(g) = (Dom(f))\\{p} and
    for any t \in Dom(g) g(t) = (f(t)-f(p)) // (t-p).

Lemma.
  Let p be an element of Dom(f).
  Then DQ(f,p) is a real map.


# DERIVATIVE
Let f denote a real map.

Definition Derivative.
  Let p be an element of Dom(f).
  D(f,p) = lim(DQ(f,p),p).

Definition.
  Let p be an element of Dom(f) that is a limit point of Dom(f).
  f is differentiable at p iff D(f,p) is a real number.

Definition.
  Let P be a subset of Dom(f).
  f is differentiable on P iff
    for any p \in P f is differentiable at p.

Lemma DerivativeOfConstantFunction.
  Let f be a real map that is defined on [x|y].
  Let c be a real number such that for any t \in [x|y] f(t) = c.
  Let p be an element of (x|y).
  Then f is differentiable at p
    and D(f,p) = 0.
Proof.
  DQ(f,p) is a real map that is defined on [x|y]\\{p} (by DifferenceQuotient).
  Let us show that for any t \in [x|y]\\{p} DQ(f,p)(t) = 0.
    Suppose t \in [x|y]\\{p}.
    Then f(t) = c = f(p).
    Then f(t)-f(p) = 0.
    Then (f(t)-f(p)) * (1/(t-p)) = 0.
    Therefore DQ(f,p)(t) = 0 (by DifferenceQuotient).
  End.
  Then lim(DQ(f,p),p)=0 (by LimitOfConstantFunction).
  D(f,p) = lim(DQ(f,p),p) (by Derivative).
  Therefore D(f,p)=0.
QED.

[prove off]
Theorem 5_3a.
  Let f be a real map such that f is defined on [x|y].
  Let g be a real map such that g is defined on [x|y].
  Let p be an element of (x|y).
  Assume that f is differentiable at p.
  Assume that g is differentiable at p.
  Then f++g is differentiable at p and
    D(f++g,p) = D(f,p) + D(g,p).

Lemma DerivativeOfScaledFunction.
  Let f be a real map.
  Let c be a real number.
  Let p be an element of Dom(f).
  Suppose that f is differentiable at p.
  Then D(c~f,p) = c * D(f,p).
# Proof!
[prove on]



# USEFUL FUNCTIONS
#Lemma ContinuityOfConstantFunction.

#Lemma DerivativeOfConstantFunction.

#Lemma ContinuityOfIdentity.

#Lemma LimitOfIdentity.

#Lemma DerivativeOfIdentity.