[read real-analysis/continuity_pre.ftl]

# Use maps instead of functions to avoid redundant checking.

################
# Map operations

Definition Codomain. Let f be a map. Let S be a class.
  f is into S iff for any x \in Dom(f) we have f(x) \in S.

Definition Composition. Let f, g be maps. Suppose f is into Dom(g).
  g \circ f is a map h such that Dom(h) = Dom(f) and
  for any x \in Dom(f) we have g(f(x)) = h(x).

Definition Preimage. Let f be a map. Let S be a class.
  f^-1(S) = {x in Dom(f) | f(x) \in S}.

Definition Injective. Let f be a map. f is injective iff
  for all x,y \in Dom(f) if f(x)=f(y) then x=y.

Definition Inverse. Let f be a injective map.
  inv(f) is a map g such that f is into Dom(g) and
  Dom(g)=f[Dom(f)] and for all x \in Dom(f) g(f(x))=x.

Definition RealMap. A real map is a map f
  such that Dom(f) \subseteq Real and f is into Real.

Definition Addition. Let f, g be real maps.
  Suppose Dom(f) = Dom(g).
  f ++ g is a map h such that Dom(h) = Dom(f) and
  for any x \in Dom(h) we have h(x) = f(x) + g(x).

Definition Multiplication. Let f, g be real maps.
  Suppose Dom(f) = Dom(g).
  f ** g is a map h such that Dom(h) = Dom(f) and
  for any x \in Dom(h) we have h(x) = f(x) * g(x).

################
# Preliminaries

Let x, y, p, q denote real numbers.
Let n, m denote positive integers.
Let eps, del denote positive real numbers.
Let E denote a subclass of Real.
Let f, g denote real maps.

Signature Distance. d(x,y) is a real number.

Axiom d1. d(x,y) = 0 iff x = y.
Axiom d2. d(x,y) = d(y,x).
Axiom d3. Let z be a real number. d(x,z)<=d(x,y)+d(y,z).

Definition Open. Let U be a subclass of E.
  U is open in E iff for any x \in U there exists eps
  such that for all y \in E if d(x,y)<eps then y \in U.

Definition Closed. Let V be a subclass of E.
  V is closed in E iff E \setminus V is open in E.

Definition Bounded. E is bounded iff E is bounded above and bounded below.

Definition Neighborhood. nbhd(p,eps) = {x in Real | d(x,p) < eps}.

Definition Sequence. A sequence is a map a
  such that Dom(a) = Natural and a is into Real.

Definition Convergence. Let a be a sequence. a converges to x
  iff for any eps there exists a positive integer N
  such that for any n if N < n then d(a(n),x) < eps.

Definition UneqConv. Let a be a sequence.
  a unequally converges to x iff for any eps there exists
  a positive integer N such that for any n if N<n then 0<d(a(n),x)<eps.

Definition LimitPoint. A limit point of E is a real number p such that
  there exists a sequence a such that a is into E and a unequally converges to p.

Definition ClosurePoint. A closure point of E is a real number p such that
  there exists a sequence a such that a is into E and a converges to p.

Definition OpenCover. An open cover of E is a map C such that Dom(C)=E and
  for all x \in E C(x) \subseteq E and C(x) is open in E and x \in C(x).

Definition FiniteSubcover. Let C be an open cover of E.
  A finite subcover of C over E is a sequence a such that a is into E
  and there exists a positive integer N such that for any x \in E
  there exists n such that n<=N and x \in C(a(n)).

Definition Compact. E is compact iff
  for any open cover C of E there exists a finite subcover of C over E.

Definition Separated. Let A, B be subclass of Real. A and B are separated
  iff for any closure point x of A x is not in B
  and for any closure point y of B y is not in A.

Definition Connected. E is connected iff
  for any nonempty A, B \subseteq Real
  if E = A \cup B then A and B are not separated.

################
# Previous results

Axiom d4. d(x,y) >= 0.
Axiom d5. If x > 0 then d(x,0) = x.

Axiom 2_18. Suppose p is not a limit point of E.
  Then there exists eps such that for all x if 0<d(x,p)<eps then x \notin E.

Axiom 2_19. nbhd(p,eps) is open in Real.

Axiom 2_28. Suppose E is nonempty and compact. There exist p, q \in E
  such that p is a greatest lower bound of E and q is a least upper bound of E.

Axiom 2_29a. Let F,V be subclass of E.
  If V is open in E then V \cap F is open in F.

Axiom 2_29b. Let F,V be subclass of E.
  If V is closed in E then V \cap F is closed in F.

Axiom 2_35. Suppose E is compact. Suppose V is a subclass of E.
  If V is closed in E then V is compact.

Axiom 2_41. E is compact iff E is bounded and closed in Real.

Axiom 2_47. E is connected iff for any x,y \in E
  for any z \in Real if x<z<y then z \in E.

Axiom 3_1. There exists a sequence a such that
  a converges to 0 and for all n a(n)>0.

Axiom 3_2. Let a be a sequence.
  If a converges to x and a converges to y then x = y.

Axiom 3_3. Let a, b be sequences.
  If a converges to x and b converges to y then
  a++b converges to x+y and a**b converges to x*y.

Axiom Min. Let a be a sequence. Let N be a positive integer.
  There exist n such that n<=N and for all m if m<=N then a(n)<=a(m).

# Consistency check
# [prove on] Lemma. Contradiction.

################
# Limits of maps

Definition 4_1. Suppose p is a limit point of Dom(f).
  lim(f,p)=q iff for any eps there exists del such that
  for any x \in Dom(f) if 0<d(x,p)<del then d(f(x),q)<eps.

Theorem 4_2. Suppose p is a limit point of Dom(f).
  lim(f,p)=q iff for any sequence a into Dom(f)
  if a unequally converges to p then f \circ a converges to q.
Proof.
  Let us show that if lim(f,p)=q then for any sequence a into Dom(f)
  if a unequally converges to p then f \circ a converges to q.
    Suppose lim(f,p)=q.
    Suppose a is a sequence such that a is into Dom(f)
    and a unequally converges to p.
    Let us show that f \circ a converges to q.
      Suppose eps is a positive real number.
      Take del such that for any x \in Dom(f) if 0<d(x,p)<del then d(f(x),q)<eps.
      Take a positive integer N such that for any n if N<n then 0<d(a(n),p)<del.
      For any n if N<n then d(f(a(n)),q)<eps.
    End.
  End.
  Let us show that if (for any sequence a if a is into Dom(f) and
  a unequally converges to p then f \circ a converges to q) then lim(f,p)=q.
    Suppose for any sequence a if a is into Dom(f) and
    a unequally converges to p then f \circ a converges to q.
    Let us show that lim(f,p)=q.
      Suppose the contrary.
      Take eps such that for any del there exists x \in Dom(f)
      such that 0<d(x,p)<del and not d(f(x),q)<eps.
      Take a sequence b such that b converges to 0 and for all n b(n)>0 (by 3_1).
      For all n d(b(n),0)=b(n) (by d5).
      Define a(n) = Choose x \in Dom(f) such that 0<d(x,p)<d(b(n),0)
      and not d(f(x),q)<eps in x for n in Natural.
      Let us show that a unequally converges to p.
        Suppose r is a positive real number.
        Take a positive integer N such that for any n if N<n then d(b(n),0)<r.
        For any n if N<n then 0<d(a(n),p)<r.
      End.
      f \circ a converges to q.
      Take a positive integer N such that
      for any n if N<n then d((f \circ a)(n),q)<eps.
      Take n such that N<n and not d(f(a(n)),q)<eps.
      Contradiction.
    End.
  End.
QED.

Theorem Uniqueness. Let q1, q2 be real numbers.
  Suppose p is a limit point of Dom(f).
  Suppose lim(f,p)=q1 and lim(f,p)=q2. Then q1 = q2.
Proof.
  Take a sequence a such that a is into Dom(f) and a unequally converges to p.
  f \circ a is a sequence.
  f \circ a converges to q1 (by 4_2).
  f \circ a converges to q2 (by 4_2).
  q1 = q2 (by 3_2).
QED.

Theorem 4_4. Suppose Dom(f) = Dom(g). Suppose p is a limit point of Dom(f).
  Let A, B be real numbers. Suppose lim(f,p)=A and lim(g,p)=B.
  Then lim(f++g,p)=A+B and lim(f**g,p)=A*B.
Proof.
  Take a class S such that Dom(f) = S.
  Take fsg = f++g. Take fmg = f**g. Take AsB=A+B. Take AmB=A*B.
  S = Dom(fsg) = Dom(fmg).
  Let us show that for any sequence a into S if a unequally converges to p
  then fsg \circ a converges to AsB and fmg \circ a converges to AmB.
    Suppose a is a sequence such that a is into S and a unequally converges to p.
    (f \circ a) and (g \circ a) are sequences.
    f \circ a converges to A (by 4_2).
    g \circ a converges to B (by 4_2).
    (f \circ a) ++ (g \circ a) converges to A+B (by 3_3).
    (f \circ a) ** (g \circ a) converges to A*B (by 3_3).
    (f \circ a) ++ (g \circ a) = fsg \circ a.
    (f \circ a) ** (g \circ a) = fmg \circ a.
  End.
  Let us show that lim(fsg,p)=AsB (by 4_2).
    For any sequence a into S if a unequally converges to p
    then fsg \circ a converges to AsB.
  End.
  Let us show that lim(fmg,p)=AmB (by 4_2).
    For any sequence a into S if a unequally converges to p
    then fmg \circ a converges to AmB.
  End.
QED.

################
# Continuous maps

Definition 4_5. Suppose p \in Dom(f). f is continuous at p
  iff for any eps there exists del such that
  for any x \in Dom(f) if d(x,p)<del then d(f(x),f(p))<eps.

Lemma 4_5a. Suppose p \in Dom(f).
  Suppose p is not a limit point of Dom(f). Then f is continuous at p.
Proof.
  Take del such that for all x if 0<d(x,p)<del then x \notin Dom(f) (by 2_18).
End.

Theorem 4_6. Suppose p \in Dom(f). Suppose p is a limit point of Dom(f).
  f is continuous at p iff lim(f,p)=f(p).

Theorem 4_7. Suppose p \in Dom(f). Suppose f is into Dom(g).
  Suppose f is continuous at p and g is continuous at f(p).
  Then g \circ f is continuous at p.
Proof.
  Suppose eps is a positive real number.
  Take del such that for any y \in Dom(g)
  if d(y,f(p))<del then d(g(y),g(f(p)))<eps.
  Take a positive real number eta such that
  for any x \in Dom(f) if d(x,p)<eta then d(f(x),f(p))<del.
  For any x \in Dom(f) if d(x,p)<eta then d(g(f(x)),g(f(p)))<eps.
QED.

Definition. f is continuous iff for all p \in Dom(f) f is continuous at p.

Theorem 4_8. Suppose f is into E.
  f is continuous iff for any subclass U of E
  if U is open in E then f^-1(U) is open in Dom(f).
Proof.
  Let us show that if f is continuous then
  for any subclass U of E if U is open in E then f^-1(U) is open in Dom(f).
    Suppose f is continuous.
    Suppose U is a subclass of E such that U is open in E.
    Let us show that f^-1(U) is open in Dom(f).
      Suppose p \in f^-1(U).
      Take eps such that for all y \in E if d(y,f(p))<eps then y \in U.
      f is continuous at p.
      Take del such that for any x \in Dom(f) if d(x,p)<del then d(f(x),f(p))<eps.
      For any x \in Dom(f) if d(x,p)<del then x \in f^-1(U).
    End.
  End.
  Let us show that if (for any subclass U of E if U is open in E
  then f^-1(U) is open in Dom(f)) then f is continuous.
    Suppose for any subclass U of E
    if U is open in E then f^-1(U) is open in Dom(f).
    Suppose p \in Dom(f).
    Let us show that f is continuous at p.
      Suppose eps is a positive real number.
      Take V = nbhd(f(p),eps) \cap E.
      V is open in E (by 2_19, 2_29a).
      Take del such that for all x \in Dom(f) if d(p,x)<del then x \in f^-1(V).
    End.
  End.
QED.

Theorem 4_9. Suppose Dom(f) = Dom(g). Suppose p \in Dom(f).
  Suppose f is continuous at p and g is continuous at p.
  Then f++g is continuous at p and f**g is continuous at p.
Proof.
  Case p is a limit point of Dom(f).
    lim(f,p)=f(p) and lim(g,p)=g(p) (by 4_6).
    lim(f++g,p)=(f++g)(p) and lim(f**g,p)=(f**g)(p) (by 4_4).
    f++g is continuous at p and f**g is continuous at p (by 4_6).
  End.
  Case p is not a limit point of Dom(f).
    f++g is continuous at p and f**g is continuous at p (by 4_5a).
  End.
QED.

################
# Continuity and Compactness

Theorem 4_14. Suppose f is continuous.
  If Dom(f) is compact then f[Dom(f)] is compact.
Proof.
  Suppose Dom(f) is compact.
  Take a subclass R of Real such that R = f[Dom(f)].
  f is into R.
  Let us show that R is compact.
    Suppose D is an open cover of R.
    Define C(x)=f^-1(D(f(x))) for x in Dom(f).
    For all x \in Dom(f) C(x) is open in Dom(f) (by 4_8).
    C is an open cover of Dom(f).
    Take a finite subcover a of C over Dom(f).
    Take a positive integer N such that for any x \in Dom(f)
    there exists n such that n<=N and x \in C(a(n)).
    Take a sequence foa such that foa = f \circ a.
    Let us show that foa is a finite subcover of D over R.
      Let us show that for any y \in R
      there exists n such that n<=N and y \in D(foa(n)).
        Suppose y \in R.
        Take x \in Dom(f) such that f(x)=y.
        Take n such that n<=N and x \in C(a(n)).
        y \in D(f(a(n))).
      End.
    End.
  End.
QED.

Lemma 4_14a. Suppose f is continuous. Suppose E \subseteq Dom(f).
  If E is compact then f[E] is compact.
Proof.
  Suppose E is compact.
  Define g(x)=f(x) for x in E.
  g is continuous.
  g[E] is compact (by 4_14).
  f[E]=g[E].
QED.

Theorem 4_16. Suppose f is continuous and Dom(f) is nonempty and compact.
  Then there exist p,q \in Dom(f) such that
  f(p) is a greatest lower bound of f[Dom(f)]
  and f(q) is a least upper bound of f[Dom(f)].
Proof.
  Take a class R such that R=f[Dom(f)].
  R is nonempty and compact (by 4_14).
  Take x,y \in R such that x is a greatest lower bound of R
  and y is a least upper bound of R (by 2_28).
  Take p,q \in Dom(f) such that f(p)=x and f(q)=y.
  f(p) is a greatest lower bound of f[Dom(f)]
  and f(q) is a least upper bound of f[Dom(f)].
QED.

Theorem 4_17. Suppose f is continuous and Dom(f) is compact.
  Suppose f is injective. Then inv(f) is continuous.
Proof.
  Take a map g such that g=inv(f).
  Take a subclass S of Real such that S=Dom(g)=f[Dom(f)].
  g is into Dom(f).
  Let us show that for any subclass U of Dom(f)
  if U is open in Dom(f) then g^-1(U) is open in S.
    Suppose U is a subclass of Dom(f) such that U is open in Dom(f).
    g^-1(U)=f[U].
    Take a class V such that V = (Dom(f)) \setminus U.
    V is closed in Dom(f).
    f[V] is compact (by 2_35, 4_14a).
    f[V] is closed in Real (by 2_41).
    f[V] \cap S is closed in S (by 2_29b).
    f[V] = f[V] \cap S.
    f[U] = S \setminus f[V].
    g^-1(U) is open in S.
  End.
  g is continuous (by 4_8).
QED.

Definition 4_18. f is uniformly continuous iff for any eps there exists del
  such that for all x,y \in Dom(f) if d(x,y)<del then d(f(x),f(y))<eps.

Corollary. If f is uniformly continuous then f is continuous.
[prove on]
Theorem 4_19. Suppose f is continuous and Dom(f) is compact.
  Then f is uniformly continuous.
Proof.
  Take E=Dom(f).
  Suppose eps is a positive real number.
  Take a positive real number ep2 such that ep2+ep2=eps.
  Define phi(y) = Choose del such that for all x \in E
  if d(x,y)<del then d(f(x),f(y))<ep2 in del for y in E.
  Define ph2(y) = Choose del such that del+del=phi(y) in del for y in E.
  Define C(y) = nbhd(y,ph2(y)) \cap E for p in E.
  Let us show that for all y \in E C(y) \subseteq E
  and C(y) is open in E and y \in C(y).
    Suppose y \in E.
    nbhd(y,ph2(y)) \cap E is open in E (by 2_19, 2_29a).
    y \in nbhd(y,ph2(y)) \cap E.
    nbhd(y,ph2(y)) \cap E = C(y).
  End.
  Take a finite subcover a of C over E.
  Take a positive integer N such that for any x \in E
  there exists n such that n<=N and x \in C(a(n)).
  Let us show that there exists del such that
  for all m if m <= N then del <= ph2(a(m)).
    ph2 \circ a is a sequence.
    Take n such that n<=N and for all m if m<=N
    then (ph2 \circ a)(n)<=(ph2 \circ a)(m) (by Min).
    Take del = (ph2 \circ a)(n).
    For all m if m<=N then del<=ph2(a(m)).
  End.
  Take del such that for all m if m <= N then del <= ph2(a(m)).
  Let us show that for all x,y \in E if d(x,y)<del then d(f(x),f(y))<eps.
    Suppose x,y \in E and d(x,y)<del.
    Take m such that m<=N and x \in C(a(m)).
    Take am=a(m).
    x \in nbhd(am,ph2(am)).
    (1) d(x,am)<ph2(am).
    Let us show that (2) for all real numbers x1,x2,y1,y2
    if x1<x2 and y1<y2 then x1+y1<x2+y2.
      Suppose x1,x2,y1,y2 are real numbers such that x1<x2 and y1<y2.
      x1+y1<x2+y1=y1+x2<y2+x2=x2+y2.
    End.
    For all real numbers x1,x2,x3 if x1<=x2 and x2<x3 then x1<x3.
    Let us show that (3) d(y,am)<phi(am).
      (4) d(y,x)<ph2(am).
      d(y,x)+d(x,am)<ph2(am)+ph2(am) (by 1,2,4).
      d(y,am)<=d(y,x)+d(x,am) (by d3).
      ph2(am)+ph2(am)=phi(am).
    End.
    (5) For all z \in E if d(z,am)<phi(am) then d(f(z),f(am))<ep2.
    ph2(am)<phi(am).
    (6) d(x,am)<phi(am).
    (7) d(f(y),f(am))<ep2 (by 3,5).
    (8) d(f(x),f(am))<ep2 (by 1,5,6).
    d(f(x),f(am))+d(f(y),f(am))<ep2+ep2 (by 2,7,8).
    d(f(x),f(y))<=d(f(x),f(am))+d(f(y),f(am)) (by d2,d3).
    d(f(x),f(y))<ep2+ep2.
  End.
QED.

################
# Continuity and Connectedness

Lemma 4_22a. p is a closure point of E
  iff p \in E or p is a limit point of E.
Proof.
  Let us show that if p is a closure point of E
  then p \in E or p is a limit point of E.
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

Theorem 4_22. Suppose f is continuous and Dom(f) is connected.
  Then f[Dom(f)] is connected.
Proof.
  Suppose the contrary.
  Take E = Dom(f).
  Take nonempty A,B \subseteq Real such that
  f[E] = A \cup B and A and B are separated.
  Take G = E \cap f^-1(A). Take H = E \cap f^-1(B).
  Let us show that for any closure point x of G x is not in H.
    Suppose the contrary.
    Take a closure point x of G such that x \in H.
    f(x) \in B.
    x \notin G (by 4_22a).
    x is a limit point of G (by 4_22a).
    Take a sequence a such that a is into G and a unequally converges to x.
    lim(f,x)=f(x) (by 4_6).
    f \circ a converges to f(x) (by 4_2).
    f \circ a is into A.
    f(x) is a closure point of A.
    Contradiction.
  End.
  Let us show that for any closure point x of H x is not in G.
    Suppose the contrary.
    Take a closure point x of H such that x \in G.
    f(x) \in A.
    x \notin H (by 4_22a).
    x is a limit point of H (by 4_22a).
    Take a sequence a such that a is into H and a unequally converges to x.
    lim(f,x)=f(x) (by 4_6).
    f \circ a converges to f(x) (by 4_2).
    f \circ a is into B.
    f(x) is a closure point of B.
    Contradiction.
  End.
  G and H are nonempty.
  E = G \cup H.
  G and H are separated.
QED.

Theorem 4_23. Suppose p<q and f is continuous and Dom(f)={s in Real|p<=s<=q}.
  Suppose f(p)<y<f(q). Then there exists x such that p<x<q and f(x)=y.
Proof.
  For any a,b \in Dom(f) for any c \in Real if a<c<b then c \in Dom(f).
  Dom(f) is connected (by 2_47).
  f[Dom(f)] is connected (by 4_22).
  y \in f[Dom(f)] (by 2_47).
QED.

################
# Discontinuities

Definition 4_25a. Suppose there exists y such that p<y
  and for all x if p<=x<y then x \in Dom(f). lim+(f,p)=q
  iff for any sequence a into Dom(f) if for all n a(n)>p
  and a converges to p then f \circ a converges to q.

Definition 4_25b. Suppose there exists y such that y<p
  and for all x if y<x<=p then x \in Dom(f). lim-(f,p)=q
  iff for any sequence a into Dom(f) if for all n a(n)<p
  and a converges to p then f \circ a converges to q.
