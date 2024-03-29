[read real-analysis/continuity_pre.ftl]

################
# Notations

Let x, y, z, p, q denote real numbers.
Let eps, del, eta denote positive real numbers.
Let m, n denote natural numbers.
Let f, g denote real maps.
Let E denote a subclass of Real.

################
# Limits of Maps

Definition 4_1. Suppose p is a limit point of Dom(f).
  lim(f,p) = q iff for any eps there exists del such that
  for any x \in Dom(f) if 0 < d(x,p) < del then d(f(x),q) < eps.

Theorem 4_2. Suppose p is a limit point of Dom(f). lim(f,p) = q iff
  for any sequence a into Dom(f) if a unequally converges to p then f \circ a converges to q.
Proof.
  If lim(f,p) = q then for any sequence a into Dom(f)
  if a unequally converges to p then f \circ a converges to q.
  Proof.
    Suppose lim(f,p) = q.
    Suppose a is a sequence such that a is into Dom(f) and a unequally converges to p.
    Let us show that f \circ a converges to q.
      Suppose eps is a positive real number.
      Take del such that for any x \in Dom(f) if 0 < d(x,p) < del then d(f(x),q) < eps (by 4_1).
      Take a natural number N such that for any n if N < n then 0 < d(a(n),p) < del.
      For any n if N < n then d(f(a(n)),q) < eps.
    End.
  End.
  If (for any sequence a if a is into Dom(f) and
  a unequally converges to p then f \circ a converges to q) then lim(f,p) = q.
  Proof.
    Suppose for any sequence a if a is into Dom(f) and
    a unequally converges to p then f \circ a converges to q.
    Let us show that lim(f,p) = q.
      Suppose the contrary.
      Take eps such that for any del there exists x \in Dom(f)
      such that 0 < d(x,p) < del and not d(f(x),q) < eps (by 4_1).
      Take a sequence b such that b converges to 0 and for all n b(n) > 0 (by 1_n).
      For all n d(b(n),0) = b(n) (by d5).
      Define a(n) = Choose x \in Dom(f) such that
      0 < d(x,p) < d(b(n),0) and not d(f(x),q) < eps in x for n in Natural.
      Let us show that a unequally converges to p.
        Suppose r is a positive real number.
        Take a natural number N such that for any n if N < n then d(b(n),0) < r.
        For any n if N < n then d(a(n),p) < r.
      End.
      f \circ a is a sequence.
      f \circ a converges to q.
      Take a natural number N such that for any n if N < n then d((f \circ a)(n),q) < eps.
      Take n such that N < n and not d(f(a(n)),q) < eps.
      Contradiction.
    End.
  End.
QED.

Theorem Uniqueness. Let q1, q2 be real numbers. Suppose p is a limit point of Dom(f).
  Suppose lim(f,p) = q1 and lim(f,p) = q2. Then q1 = q2.
Proof.
  Take a sequence a such that a is into Dom(f) and a unequally converges to p.
  f \circ a is a sequence.
  f \circ a converges to q1 (by 4_2).
  f \circ a converges to q2 (by 4_2).
  q1 = q2 (by 3_2).
QED.

Theorem 4_4a. Suppose Dom(f) = Dom(g). Suppose p is a limit point of Dom(f).
  Suppose lim(f,p) = x and lim(g,p) = y. Then lim(f++g,p) = x + y.
Proof.
  Dom(f) = Dom(f ++ g).
  For any sequence a into Dom(f)
  if a unequally converges to p then (f ++ g) \circ a converges to x + y.
  Proof.
    Suppose a is a sequence such that a is into Dom(f) and a unequally converges to p.
    (f \circ a) and (g \circ a) are sequences.
    f \circ a converges to x (by 4_2).
    g \circ a converges to y (by 4_2).
    (f \circ a) ++ (g \circ a) converges to x + y (by 3_3a).
    (f \circ a) ++ (g \circ a) = (f ++ g) \circ a.
  End.
  lim(f++g,p) = x + y (by 4_2).
QED.

Theorem 4_4b. Suppose Dom(f) = Dom(g). Suppose p is a limit point of Dom(f).
  Suppose lim(f,p) = x and lim(g,p) = y. Then lim(f**g,p) = x * y.
Proof.
  Dom(f) = Dom(f ** g).
  For any sequence a into Dom(f)
  if a unequally converges to p then (f ** g) \circ a converges to x * y.
  Proof.
    Suppose a is a sequence such that a is into Dom(f) and a unequally converges to p.
    (f \circ a) and (g \circ a) are sequences.
    f \circ a converges to x (by 4_2).
    g \circ a converges to y (by 4_2).
    (f \circ a) ** (g \circ a) converges to x * y (by 3_3b).
    (f \circ a) ** (g \circ a) = (f ** g) \circ a.
  End.
  lim(f**g,p) = x * y (by 4_2).
QED.

Theorem 4_4c. Suppose Dom(f) = Dom(g). Suppose p is a limit point of Dom(g).
  Suppose for all z \in Dom(g) g(z) != 0. Suppose lim(f,p) = x. Suppose lim(g,p) = y and y != 0.
  Then lim(f|//|g,p) = x // y.
Proof.
  For any sequence a into Dom(g)
  if a unequally converges to p then 1|/|g \circ a converges to 1/y.
  Proof.
    Suppose a is a sequence such that a is into Dom(g) and a unequally converges to p.
    1|/|g \circ a is a sequence.
    g \circ a converges to y (by 4_2).
    For any n we have (g \circ a)(n) != 0.
    1|/|(g \circ a) converges to 1/y (by 3_3c).
    1|/|g \circ a = 1|/|(g \circ a).
  End.
  lim(1|/|g,p) = 1/y (by 4_2).
  lim(f|//|g,p) = x // y (by 4_4b).
QED.

################
# Continuous Maps

Definition 4_5. Suppose p \in Dom(f).
  f is continuous at p iff for any eps there exists del
  such that for any x \in Dom(f) if d(x,p) < del then d(f(x),f(p)) < eps.

Lemma 4_5a. Suppose p \in Dom(f). Suppose p is not a limit point of Dom(f).
  Then f is continuous at p.
Proof.
  Take del such that for all x if 0 < d(x,p) < del then x \notin Dom(f) (by 2_18).
QED.

Theorem 4_6. Suppose p \in Dom(f). Suppose p is a limit point of Dom(f).
  f is continuous at p iff lim(f,p) = f(p).

Theorem 4_7. Suppose p \in Dom(f). Suppose f is into Dom(g).
  Suppose f is continuous at p. Suppose g is continuous at f(p).
  Then g \circ f is continuous at p.
Proof.
  Suppose eps is a positive real number.
  Take del such that for any y \in Dom(g) if d(y,f(p)) < del then d(g(y),g(f(p))) < eps.
  Take eta such that for any x \in Dom(f) if d(x,p) < eta then d(f(x),f(p)) < del.
  For any x \in Dom(f) if d(x,p) < eta then d(g(f(x)),g(f(p))) < eps.
QED.

Definition. f is continuous iff for all p \in Dom(f) f is continuous at p.

Theorem 4_8. Suppose f is into E.
  f is continuous iff for any subclass U of E if U is open in E then f^-1(U) is open in Dom(f).
Proof.
  If f is continuous then for any subclass U of E
  if U is open in E then f^-1(U) is open in Dom(f).
  Proof.
    Suppose f is continuous.
    Suppose U is a subclass of E such that U is open in E.
    Let us show that f^-1(U) is open in Dom(f).
      Suppose p \in f^-1(U).
      Take eps such that for all y \in E if d(y,f(p)) < eps then y \in U.
      Take del such that for any x \in Dom(f) if d(x,p) < del then d(f(x),f(p)) < eps.
      For any x \in Dom(f) if d(x,p) < del then x \in f^-1(U).
    End.
  End.
  If for any subclass U of E if U is open in E then f^-1(U) is open in Dom(f)
  then f is continuous.
  Proof.
    Suppose for any subclass U of E if U is open in E then f^-1(U) is open in Dom(f).
    Suppose p \in Dom(f).
    Let us show that f is continuous at p.
      Suppose eps is a positive real number.
      Take V = nbhd(f(p),eps) \cap E.
      V is open in E (by 2_19, 2_29a).
      Take del such that for all x \in Dom(f) if d(p,x) < del then x \in f^-1(V).
    End.
  End.
QED.

Theorem 4_9. Suppose Dom(f) = Dom(g). Suppose p \in Dom(f).
  Suppose f and g are continuous at p.
  Then f ++ g and f ** g are continuous at p.
Proof.
  Case p is a limit point of Dom(f).
    lim(f,p) = f(p) and lim(g,p) = g(p) (by 4_6).
    lim(f++g,p) = (f ++ g)(p) and lim(f**g,p) = (f ** g)(p) (by 4_4a, 4_4b).
    f ++ g is continuous at p and f ** g is continuous at p (by 4_6).
  End.
  Case p is not a limit point of Dom(f).
    f ++ g is continuous at p and f ** g is continuous at p (by 4_5a).
  End.
QED.

################
# Continuity and Compactness

Theorem 4_14. Suppose f is continuous. Suppose Dom(f) is compact. Then f[Dom(f)] is compact.
Proof.
  Take T \subseteq Real such that T = f[Dom(f)].
  Let us show that T is compact.
    Suppose D is a neighborhood cover of T.
    For any x \in Dom(f) f^-1(D(f(x))) is a set.
    Define G(x) = f^-1(D(f(x))) for x in Dom(f).
    For all x \in Dom(f) G(x) is open in Dom(f) (by 4_8).
    G is a neighborhood cover of Dom(f).
    Indeed for all x \in Dom(f) G(x) is open in Dom(f) (by 4_8).
    Take a finite subcover a of G on Dom(f).
    Take a natural number N such that N > 1 and
    for any x \in Dom(f) there exists n such that n < N and x \in G(a(n)).
    Let us show that f \circ a is a finite subcover of D on T.
      Let us show that for any y \in T there exists n such that n < N and y \in D(f(a(n))).
        Suppose y \in T.
        Take x \in Dom(f) such that f(x) = y.
        Take n such that n < N and x \in G(a(n)).
        y \in D(f(a(n))).
      End.
      f \circ a is into T.
    End.
  End.
QED.

Lemma 4_14a. Suppose f is continuous. Suppose E is a compact subclass of Dom(f).
  Then f[E] is compact.
Proof.
  Define g(x) = f(x) for x in E.
  Let us show that for any x \in E g is continuous at x.
    Suppose x \in E.
    f is continuous at x.
    g is continuous at x (by 4_5).
  End.
  g[E] is compact (by 4_14).
  f[E] = g[E].
QED.

Theorem 4_16. Suppose f is continuous. Suppose Dom(f) is nonempty and compact.
  Then there exist p, q \in Dom(f) such that
  f(p) is the supremum of f[Dom(f)] and f(q) is the infimum of f[Dom(f)].
Proof.
  Take a class R such that R = f[Dom(f)].
  R is nonempty and compact (by 4_14).
  Take x, y \in R such that x is the supremum of R and y is the infimum of R (by 2_28).
  Take p, q \in Dom(f) such that f(p) = x and f(q) = y.
  f(p) is the supremum of R and f(q) is the infimum of R.
QED.

Theorem 4_17. Suppose f is continuous and injective.
  Suppose Dom(f) is compact. Then inv(f) is continuous.
Proof.
  Take a map g such that g = inv(f).
  Dom(g) = f[Dom(f)].
  g is into Dom(f).
  For any U \subseteq Dom(f) if U is open in Dom(f) then g^-1(U) is open in Dom(g).
  Proof.
    Suppose U is a subclass of Dom(f) such that U is open in Dom(f).
    Take a class V such that V = (Dom(f)) \setminus U.
    f[V] is compact (by 2_35, 4_14a). Indeed V is closed in Dom(f).
    Let us show that f[V] is closed in Dom(g).
      f[V] is closed in Real (by 2_41).
      f[V] \cap Dom(g) is closed in Dom(g) (by 2_29b).
      f[V] = f[V] \cap Dom(g).
    End.
    f[U] is open in Dom(g). Indeed f[U] = (Dom(g)) \setminus f[V].
    g^-1(U) = f[U].
  End.
  g is continuous (by 4_8).
QED.

Definition 4_18. f is uniformly continuous iff for any eps there exists del
  such that for all x,y \in Dom(f) if d(x,y) < del then d(f(x),f(y)) < eps.

Corollary. If f is uniformly continuous then f is continuous.

Theorem 4_19. Suppose f is continuous. Suppose Dom(f) is compact.
  Then f is uniformly continuous.
Proof.
  Take E = Dom(f).
  Suppose eps is a positive real number.
  Take a positive real number ep2 such that ep2 + ep2 = eps.
  Define phi(y) = Choose del such that
  for all x \in E if d(x,y) < del then d(f(x),f(y)) < ep2 in del for y in E.
  Define ph2(y) = Choose del such that del + del = phi(y) in del for y in E.
  For any y \in E nbhd(y,ph2(y)) \cap E is a set.
  Define G(y) = nbhd(y,ph2(y)) \cap E for y in E.
  Let us show that G is a neighborhood cover of E.
    Let us show that for all y \in E G(y) \subseteq E and G(y) is open in E and y \in G(y).
      Suppose y \in E.
      nbhd(y,ph2(y)) \cap E is open in E (by 2_19, 2_29a).
      y \in nbhd(y,ph2(y)) \cap E.
      nbhd(y,ph2(y)) \cap E = G(y).
    End.
  End.
  Take a finite subcover a of G on E.
  Take a natural number N such that N > 1 and
  for any x \in E there exists n such that n < N and x \in G(a(n)).
  Let us show that there exists del such that for all m if m < N then del <= ph2(a(m)).
    ph2 \circ a is a sequence.
    Take n such that n < N and for all m if m < N
    then (ph2 \circ a)(n) <= (ph2 \circ a)(m) (by Min).
    Take del = (ph2 \circ a)(n).
    For all m if m < N then del <= ph2(a(m)).
  End.
  Take del such that for all m if m < N then del <= ph2(a(m)).
  Let us show that for all x, y \in E if d(x,y) < del then d(f(x),f(y)) < eps.
    Suppose x, y \in E and d(x,y) < del.
    Take m such that m < N and x \in G(a(m)).
    Take am = a(m).
    d(x,am) < ph2(am). Indeed x \in nbhd(am,ph2(am)).
    (1) For all real numbers x1, x2, y1, y2 if x1 < x2 and y1 < y2 then x1 + y1 < x2 + y2.
    Proof.
      Suppose x1, x2, y1, y2 are real numbers such that x1 < x2 and y1 < y2.
      x1 + y1 < x2 + y1 = y1 + x2 < y2 + x2 = x2 + y2.
    End.
    Let us show that (2) d(y,am) < phi(am).
      d(y,am) <= d(y,x) + d(x,am) (by d3).
      d(y,x) + d(x,am) < ph2(am) + ph2(am) (by 1). Indeed d(y,x) < ph2(am).
      ph2(am) + ph2(am) = phi(am).
    End.
    (3) For all z \in E if d(z,am) < phi(am) then d(f(z),f(am)) < ep2.
    (4) d(x,am) < phi(am). Indeed ph2(am) < phi(am).
    (5) d(f(y),f(am)) < ep2 (by 2,3).
    (6) d(f(x),f(am)) < ep2 (by 3,4).
    d(f(x),f(y)) <= d(f(x),f(am)) + d(f(y),f(am)) (by d2, d3).
    d(f(x),f(am)) + d(f(y),f(am)) < ep2 + ep2 (by 1, 5, 6).
    d(f(x),f(y)) < ep2 + ep2.
  End.
QED.

################
# Continuity and Connectedness

Lemma 4_22a. p is a closure point of E iff p \in E or p is a limit point of E.
Proof.
  If p is a closure point of E then p \in E or p is a limit point of E.
  Proof.
    Suppose p is a closure point of E and p \notin E.
    Take a sequence a such that a is into E and a converges to p.
    a unequally converges to p.
  End.
  If p is a limit point of E then p is a closure point of E.
  Let us show that if p \in E then p is a closure point of E.
    Suppose p \in E.
    Define a(n) = p for n in Natural.
    a is into E and a converges to p.
  End.
QED.

Theorem 4_22. Suppose f is continuous. Suppose Dom(f) is connected. Then f[Dom(f)] is connected.
Proof.
  Suppose the contrary.
  Take E = Dom(f).
  Take nonempty A, B \subseteq Real such that f[E] = A \cup B and A and B are separated.
  Take G = E \cap f^-1(A). Take H = E \cap f^-1(B).
  Let us show that for any closure point x of G x is not in H.
    Suppose the contrary.
    Take a closure point x of G such that x \in H.
    x is a limit point of G (by 4_22a). Indeed x \notin G.
    Take a sequence a such that a is into G and a unequally converges to x.
    lim(f,x) = f(x) (by 4_6).
    f \circ a converges to f(x) (by 4_2).
    f \circ a is into A.
    f(x) is a closure point of A.
    Contradiction.
  End.
  Let us show that for any closure point x of H x is not in G.
    Suppose the contrary.
    Take a closure point x of H such that x \in G.
    x is a limit point of H (by 4_22a). Indeed x \notin H.
    Take a sequence a such that a is into H and a unequally converges to x.
    lim(f,x) = f(x) (by 4_6).
    f \circ a converges to f(x) (by 4_2).
    f \circ a is into B.
    f(x) is a closure point of B.
    Contradiction.
  End.
  G and H are nonempty.
  E = G \cup H.
  G and H are separated.
  Dom(f) is not connected.
  Contradiction.
QED.

Theorem 4_23. Suppose p < q. Suppose Dom(f) = { s in Real | p <= s <= q }.
  Suppose f is continuous. Suppose f(p) < y < f(q).
  Then there exists x such that p < x < q and f(x) = y.
Proof.
  Dom(f) is connected (by 2_47).
  Indeed for any a, b \in Dom(f) for any c \in Real if a < c < b then c \in Dom(f).
  f[Dom(f)] is connected (by 4_22).
  y \in f[Dom(f)] (by 2_47).
  Take x \in Dom(f) such that f(x) = y.
QED.
