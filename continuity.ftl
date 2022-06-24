[read real-analysis/numbers.ftl]
[read real-analysis/vocabulary.ftl]

# Use maps instead of functions to avoid redundant checking.

################
# Map operations

Definition Codomain. Let f be a map.
Let S be a class. f is into S iff
for any x \in Dom(f) we have f(x) \in S.

Definition Composition. Let f, g be maps.
Suppose f is into Dom(g). g \circ f is a map h
such that Dom(h) = Dom(f) and for any x \in Dom(f)
we have g(f(x)) = h(x).

Definition Preimage. Let f be a map.
Let S be a class.
f^-1(S) = {x in Dom(f) | f(x) \in S}.

Definition Addition. Let f, g be maps into Real.
Suppose Dom(f) = Dom(g).
f ++ g is a map h such that Dom(h) = Dom(f) and
for any x \in Dom(h) we have h(x) = f(x) + g(x).

Definition Multiplication. Let f, g be maps into Real.
Suppose Dom(f) = Dom(g).
f ** g is a map h such that Dom(h) = Dom(f) and
for any x \in Dom(h) we have h(x) = f(x) * g(x).

################
# Preliminaries

Let x, y, p, q denote real numbers.
Let n, m denote positive integers.
Let eps, del denote positive real numbers.

Signature Distance. d(x,y) is a real number.

Definition Open. Let E be a subset of Real.
E is open iff for any x \in E there exists eps
such that for all y if d(x,y)<eps then y \in E.

Definition Sequence. A sequence is a map a
such that Dom(a) = Natural and a is into Real.

Definition Convergence. Let a be a sequence.
a converges to x iff
for any eps there exists a positive integer N
such that for any n
if N < n then d(a(n),x) < eps.

Definition LimitPoint. Let E be a subset of Real.
A limit point of E is a real number p such that
there exists a sequence a such that
(for all n a(n) != p) and
(a is into E) and (a converges to p).

################
# Limits of maps

Definition RealMap. A real map is a map f
such that Dom(f) \subseteq Real and f is into Real.

Let f, g denote real maps.

Definition 4_1. Suppose p is a limit point of Dom(f).
lim(f,p)=q iff for any eps there exists del such that
for any x \in Dom(f) if d(x,p)<del then d(f(x),q)<eps.

#TODO
Axiom 4_2. Suppose p is a limit point of Dom(f).
lim(f,p)=q iff for any sequence a into Dom(f)
if (for all n a(n) != p) and (a converges to p)
then f \circ a converges to q.

#TODO
Axiom Uniqueness. Let q1, q2 be real numbers.
Suppose p is a limit point of Dom(f).
Suppose lim(f,p)=q1 and lim(f,p)=q2.
Then q1 = q2.

#TODO
Axiom 4_4. Suppose Dom(f) = Dom(g).
Suppose p is a limit point of Dom(f).
Let A, B be real numbers.
Suppose lim(f,p)=A and lim(g,p)=B.
Then lim(f++g,p) = A+B and lim(f**g,p) = A*B.

################
# Continuous maps

Definition 4_5. Suppose p \in Dom(f).
f is continuous at p iff for any eps there exists del
such that for any x \in Dom(f)
if d(x,p)<del then d(f(x),f(p))<eps.

Theorem 4_6. Suppose p \in Dom(f).
Suppose p is a limit point of Dom(f).
f is continuous at p iff lim(f,p)=f(p).

#TODO
Axiom 4_7. Suppose p \in Dom(f).
Suppose f is into Dom(g).
Suppose f is continuous at p and g is continuous at f(p).
Then g \circ f is continuous at p.

Definition. f is continuous iff
for all p \in Dom(f) f is continuous at p.

#TODO
Axiom 4_8. Suppose Dom(f) = Real. f is continuous
iff for any open subset E of Real f^-1(E) is open.

#TODO
Axiom 4_9. Suppose Dom(f) = Dom(g).
Suppose f is continuous and g is continuous.
Then f++g is continuous and f**g is continuous.
