[read real-analysis/numbers.ftl]
[read real-analysis/vocabulary.ftl]

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

Axiom d1. d(x,y) = 0 iff x = y.
Axiom d2. d(x,y) = d(y,x).
Axiom d3. Let z be a real number. d(x,z)<=d(x,y)+d(y,z).

Definition Open. Let E be a subset of Real.
  E is open iff for any x \in E there exists eps
  such that for all y if d(x,y)<eps then y \in E.

Definition Neighborhood. nbhd(p,eps) = {x in Real | d(x,p) < eps}.

Definition Sequence. A sequence is a map a
  such that Dom(a) = Natural and a is into Real.

Definition Convergence. Let a be a sequence. a converges to x
  iff for any eps there exists a positive integer N
  such that for any n if N < n then d(a(n),x) < eps.

Definition UneqConv. Let a be a sequence.
  a unequally converges to x iff for any eps there exists
  a positive integer N such that for any n if N<n then 0<d(a(n),x)<eps.

Definition LimitPoint. Let E be a subset of Real.
  A limit point of E is a real number p such that there exists
  a sequence a such that a is into E and a unequally converges to p.

################
# Previous results

Axiom d4. d(x,y) >= 0.
Axiom d5. If x > 0 then d(x,0) = x.

Axiom NbhdOpen. nbhd(p,eps) is open.

Axiom IsoPt. Let E be a subset of Real. Suppose p is not a limit point of E.
  Then there exists eps such that for all x if 0<d(x,p)<eps then x \notin E.

Axiom 3_1. There exists a sequence a such that
  a converges to 0 and for all n a(n)>0.

Axiom 3_2. Let a be a sequence.
  If a converges to x and a converges to y then x = y.

Axiom 3_3. Let a, b be sequences.
  If a converges to x and b converges to y then
  a++b converges to x+y and a**b converges to x*y.

################
# Limits of maps

Definition RealMap. A real map is a map f
  such that Dom(f) \subseteq Real and f is into Real.

Let f, g denote real maps.

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
  Suppose p is a limit point of Dom(f). Suppose lim(f,p)=q1 and lim(f,p)=q2.
  Then q1 = q2.
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
  Take fsg = f++g. Take fmg = f**g.
  S = Dom(fsg) = Dom(fmg).
  Let us show that for any sequence a into S if a unequally converges to p
  then fsg \circ a converges to A+B and fmg \circ a converges to A*B.
    Suppose a is a sequence such that a is into S and a unequally converges to p.
    (f \circ a) and (g \circ a) are sequences.
    f \circ a converges to A (by 4_2).
    g \circ a converges to B (by 4_2).
    (f \circ a) ++ (g \circ a) = fsg \circ a.
    fsg \circ a converges to A+B (by 3_3).
    (f \circ a) ** (g \circ a) = fmg \circ a.
    fmg \circ a converges to A*B (by 3_3).
  End.
  lim(fsg,p)=A+B (by 4_2).
  lim(fmg,p)=A*B (by 4_2).
QED.

################
# Continuous maps

Definition 4_5. Suppose p \in Dom(f). f is continuous at p
  iff for any eps there exists del such that
  for any x \in Dom(f) if d(x,p)<del then d(f(x),f(p))<eps.

Lemma 4_5a. Suppose p \in Dom(f).
  Suppose p is not a limit point of Dom(f). Then f is continuous at p.
Proof.
  Take del such that for all x if 0<d(x,p)<del then x \notin Dom(f).
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
QED.

Definition. f is continuous iff
  for all p \in Dom(f) f is continuous at p.

Theorem 4_8. Suppose Dom(f) = Real. f is continuous
  iff for any open subset E of Real f^-1(E) is open.
Proof.
  Let us show that if f is continuous then
  for any open subset E of Real f^-1(E) is open.
    Suppose f is continuous.
    Suppose E is an open subset of Real.
    Let us show that f^-1(E) is open.
      Suppose p \in f^-1(E).
      Take eps such that for all y if d(f(p),y)<eps then y \in E.
      f is continuous at p.
      Take del such that for any x if d(x,p)<del then d(f(x),f(p))<eps.
    End.
  End.
  Let us show that if for any open subset E of Real
  f^-1(E) is open then f is continuous.
    Suppose for any open subset E of Real f^-1(E) is open.
    Suppose p \in Dom(f).
    Let us show that f is continuous at p.
      Suppose eps is a positive real number.
      Take V = nbhd(f(p),eps).
      f^-1(V) is open (by NbhdOpen).
      Take del such that for all x if d(p,x)<del then x \in f^-1(V).
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