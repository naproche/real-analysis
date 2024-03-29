[read preliminaries.ftl]
[read real-analysis/numbers.ftl]

# Map operations
Let f denote a map.

Definition Codomain.
  Let S be a class.
  f is into S iff for any x \in Dom(f) we have f(x) \in S.

Definition Image. Suppose M \subseteq Dom(f). f[M] = { f(j) | j \in M }.

Definition Composition. Let f, g be maps. Suppose f is into Dom(g).
  g \circ f is a map h such that Dom(h) = Dom(f) and
  for any x \in Dom(f) we have g(f(x)) = h(x).

Definition Preimage. Let f be a map. Let S be a class.
  f^-1(S) = {x in Dom(f) | f(x) \in S}.

Definition Addition. Let f, g be maps into Real.
  Suppose Dom(f) = Dom(g).
  f ++ g is a map h such that Dom(h) = Dom(f) and
  for any x \in Dom(h) we have h(x) = f(x) + g(x).

Definition Multiplication. Let f, g be maps into Real.
  Suppose Dom(f) = Dom(g).
  f ** g is a map h such that Dom(h) = Dom(f) and
  for any x \in Dom(h) we have h(x) = f(x) * g(x).

Definition Division. Let f, g be maps into Real.
  Suppose Dom(f) = Dom(g). 
  Suppose g(x) != 0 for every x \in Dom(g).
  f|//|g is a map h such that Dom(h) = Dom(f) and
  for any x \in Dom(h) we have h(x) = f(x)//g(x).


################
# Preliminaries

Let x, y, p, q denote real numbers.
Let n, m denote positive integers.
Let eps, del denote positive real numbers.


# Compactness
# This differs from continuity_pre.ftl but Freddy didn't want to introduce open covers etc.
Signature.
  Let S be a subset of Real.
  S is compact is an atom.

Signature Distance. d(x,y) is a real number.

Axiom d1. d(x,y) = 0 iff x = y.
Axiom d2. d(x,y) = d(y,x).
Axiom d3. Let z be a real number. d(x,z)<=d(x,y)+d(y,z).
Axiom d4. Let c be a positive real number. d(x,y) < c iff y-c < x < y+c.

Definition Sequence. A sequence is a map a
  such that Dom(a) = Natural and a is into Real.

Definition UneqConv. Let a be a sequence.
  a unequally converges to x iff for any eps there exists
  a positive integer N such that for any n if N<n then 0<d(a(n),x)<eps.

Definition LimitPoint. Let E be a subclass of Real.
  A limit point of E is a real number p such that there exists
  a sequence a such that a is into E and a unequally converges to p.

Definition RealMap. A real map is a map f
  such that Dom(f) \subseteq Real and f is into Real.

Let f, g denote real map.

Definition 4_1. Suppose p is a limit point of Dom(f).
  lim(f,p)=q iff for any positive real number eps there exists positive real number del such that
  for any x \in Dom(f) if 0<d(x,p)<del then d(f(x),q)<eps.

Definition 4_5. Suppose p \in Dom(f). f is continuous at p
  iff for any eps there exists del such that
  for any x \in Dom(f) if d(x,p)<del then d(f(x),f(p))<eps.

Definition 4_1b. f is continuous iff for all p \in Dom(f) f is continuous at p.


[prove off]
Theorem 4_6. Suppose p \in Dom(f). Suppose p is a limit point of Dom(f).
  f is continuous at p iff lim(f,p)=f(p).

Theorem 4_4. Suppose Dom(f) = Dom(g). Suppose p is a limit point of Dom(f).
  Let A, B be real numbers. Suppose lim(f,p)=A and lim(g,p)=B.
  Then lim(f++g,p)=A+B and lim(f**g,p)=A*B.

Theorem 4_9. Suppose Dom(f) = Dom(g). Suppose p \in Dom(f).
  Suppose f is continuous at p and g is continuous at p.
  Then f ++ g is continuous at p and f ** g is continuous at p.


# Freddy changed this theorem because he was not able to copy the defintions of upper bounds, supremum, etc.
Theorem 4_16.
  Suppose f is continuous and Dom(f) is nonempty and compact.
  Then (there exists p \in Dom(f) such that
    for any t \in Dom(f) f(t) <= f(p)) and
  there exists q \in Dom(f) such that
    for any t \in Dom(f) f(t) >= f(q).
[prove on]