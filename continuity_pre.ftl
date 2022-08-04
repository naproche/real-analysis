[read real-analysis/vocabulary.ftl]
[read vocabulary.ftl]
[read macros.ftl]

# Classes

Let S, T denote classes.
Let i, j denote objects.
Let j \in S denote j is an element of S.
Let j \notin S denote j is not an element of S.

Definition. A subclass of S is a class T such that every element of T belongs to S.
Let T \subseteq S denote T is a subclass of S.

Definition. S \cup T is a class U such that for any j (j \in U) iff (j \in S or j \in T).
Definition. S \cap T = { j in S | j \in T }.
Definition. S \setminus T = { j in S | j \notin T }.
Definition. S is nonempty iff S has an element.

# Maps

Let f, g denote maps.

Definition Codomain. f is into S iff for any j \in Dom(f) we have f(j) \in S.

Definition Image. Suppose M \subseteq Dom(f). f[M] = { f(j) | j \in M }.

Definition Composition. Suppose f is into Dom(g). g \circ f is a map h
  such that Dom(h) = Dom(f) and for any j \in Dom(f) we have g(f(j)) = h(j).

Definition Preimage. f^-1(S) = { j in Dom(f) | f(j) \in S }.

Definition Injective. f is injective iff for any i, j \in Dom(f) if f(i) = f(j) then i = j.

Definition Inverse. Suppose f is injective. inv(f) is a map g such that
  f is into Dom(g) and Dom(g) = f[Dom(f)] and for all j \in Dom(f) g(f(j)) = j.

# Real numbers

Signature. A real number is a mathematical object.

Let x, y, z denote real numbers.

Definition Real. Real is the collection of real numbers.

Axiom Subset. Any subclass of Real is a set.

Signature 1_12_A. x + y is a real number.
Axiom 1_12_A2. x + y = y + x.
Axiom 1_12_A3. (x + y) + z = x + (y + z).
Signature 1_12_A4. 0 is a real number such that for every real number x we have x + 0 = x.
Signature 1_12_A5. -x is a real number such that x + (-x) = 0.

Signature 1_12_M. x * y is a real number.
Axiom 1_12_M2. x * y = y * x.
Axiom 1_12_M3. (x * y) * z = x * (y * z).
Signature 1_12_M4. 1 is a real number such that 1 != 0
  and for every real number x we have x * 1 = x.
Signature 1_12_M5. Assume x != 0. 1/x is a real number such that x * 1/x = 1.

Axiom 1_12_D. x * (y + z) = (x * y) + (x * z).
Axiom 1_14. If x + y = x + z then y = z.
Axiom 1_15. If x != 0 and x * y = x * z then y = z.

Let x - y denote x + (-y).
Let x // y denote x * 1/y.

# Order

Signature 1_5. x < y is an atom.
Let x > y denote y < x.
Let x <= y denote x < y or x = y.
Let x >= y denote y <= x.

Axiom 1_5_a. not x < x.
Axiom 1_5_b. If x < y and y < z then x < z.
Axiom 1_5_c. If x != y then x < y or y < x.

Axiom 1_17. If x < y then x + z < y + z.
Axiom 1_18. If z > 0 and x < y then x * z < y * z.

Axiom 1_20. If y > 0 then there exists x such that x > 0 and x + x = y.

Let x is positive denote x > 0.
Let x is negative denote x < 0.

# Upper and lower bounds

Let E denote a subclass of Real.

Definition 1_7a. An upper bound of E is a real number p such that for all x \in E x <= p.
Let E is bounded above denote E has an upper bound.
Definition 1_7b. A lower bound of E is a real number p such that for all x \in E x >= p.
Let E is bounded below denote E has a lower bound.
Definition 1_7c. E is bounded iff E is bounded above and bounded below.

Definition 1_8a. A supremum of E is a real number p such that
  p is an upper bound of E and for all x if x < p then x is not an upper bound of E.
Definition 1_8b. An infimum of E is a real number p such that
  p is a lower bound of E and for all x if x > p then x is not a lower bound of E.

# Natural numbers.

Signature. A natural number is a real number.

Let m, n denote natural numbers.

Definition Natural. Natural is the collection of natural numbers.

Axiom. 1 is a natural number.
Axiom. m + 1 is a natural number.
Axiom. If n > 1 then there exists m such that m + 1 = n.
Axiom. n >= 1.

# Real maps

Definition RealMap. A real map is a map f such that Dom(f) \subseteq Real and f is into Real.

Definition Addition. Suppose f, g are real maps such that Dom(f) = Dom(g).
  f ++ g is a map h such that Dom(h) = Dom(f) and for any x \in Dom(h) we have h(x) = f(x) + g(x).

Definition Multiplication. Suppose f, g are real maps such that Dom(f) = Dom(g).
  f ** g is a map h such that Dom(h) = Dom(f) and for any x \in Dom(h) we have h(x) = f(x) * g(x).

# Metric

Signature Distance. d(x,y) is a real number.

Axiom d1. d(x,y) = 0 iff x = y.
Axiom d2. d(x,y) = d(y,x).
Axiom d3. d(x,z) <= d(x,y) + d(y,z).
Axiom d4. d(x,y) >= 0.
Axiom d5. If x > 0 then d(x,0) = x.

# Sequences

Definition Sequence. A sequence is a map a such that Dom(a) = Natural and a is into Real.

Let a, b denote a sequences.
Let eps, del denote positive real numbers.
Let N denote a natural number.

Axiom Min. Suppose N > 1.
  There exists n such that n < N and for all m if m < N then a(n) <= a(m).

Definition Convergence. a converges to x iff for any eps
  there exists N such that for any n if n > N then d(a(n),x) < eps.

Definition UneqConv. a unequally converges to x iff for any eps
  there exists N such that for any n if n > N then 0 < d(a(n),x) < eps.

Axiom 3_1. There exists a sequence a such that a converges to 0 and for all n a(n) > 0.

Axiom 3_2. If a converges to x and a converges to y then x = y.

Axiom 3_3. If a converges to x and b converges to y
  then a ++ b converges to x + y and a ** b converges to x * y.

# Basic Topology

Definition Open. Let U be a subclass of E. U is open in E iff
  for any x \in U there exists eps such that for any y \in E if d(x,y) < eps then y \in U.

Definition Closed. Let V be a subclass of E. V is closed in E iff E \setminus V is open in E.

Axiom 2_29a. Let F, V be subclass of E. If V is open in E then V \cap F is open in F.

Axiom 2_29b. Let F, V be subclass of E. If V is closed in E then V \cap F is closed in F.

Definition LimitPoint. A limit point of E is a real number p such that
  there exists a sequence a such that a is into E and a unequally converges to p.

Definition ClosurePoint. A closure point of E is a real number p such that
  there exists a sequence a such that a is into E and a converges to p.

Axiom 2_18. Suppose y is not a limit point of E.
  Then there exists eps such that for all x if 0 < d(x,y) < eps then x \notin E.

Definition Neighborhood. nbhd(y,eps) = { x in Real | d(x,y) < eps }.

Axiom 2_19. nbhd(y,eps) is open in Real.

# Compactness

Definition OpenCover. An open cover of E is a map C such that Dom(C) = E
  and for any x \in E C(x) \subseteq E and C(x) is open in E and x \in C(x).

Definition FiniteSubcover. Let C be an open cover of E.
  A finite subcover of C on E is a sequence a such that a is into E and there exists N
  such that N > 1 and for any x \in E there exists n such that n < N and x \in C(a(n)).

Definition Compact. E is compact iff
  for any open cover C of E there exists a finite subcover of C on E.

Axiom 2_28. Suppose E is nonempty and compact.
  There exist p, q \in E such that p is the supremum of E and q is the infimum of E.

Axiom 2_35. Suppose E is compact. Suppose V \subseteq E.
  If V is closed in E then V is compact.

Axiom 2_41. E is compact iff E is bounded and closed in Real.

# Connectedness

Definition Separated. Let A, B \subseteq Real. A and B are separated iff
  any closure point of A is not in B and any closure point of B is not in A.

Definition Connected. E is connected iff
  for any nonempty A, B \subseteq Real if E = A \cup B then A and B are not separated.

Axiom 2_47. E is connected iff for any x, y \in E for any z if x < z < y then z \in E.

# Consistency check
# [timelimit 20] Lemma. Contradiction.