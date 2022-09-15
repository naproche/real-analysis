[prove off]
[check off]
[read preliminaries.ftl]
[read real-analysis/numbers.ftl]

Definition Codomain.
  Let S be a class.
  Let f be a map.
  f is into S iff for any x \in Dom(f) we have f(x) \in S.

Definition RealMap.
  A real map is a map f such that
    Dom(f) \subseteq Real and f is into Real.

Let x,y denote real numbers.
Signature Distance. d(x,y) is a real number.

Definition LimitPoint.
  Let E be a subclass of Real.
  A limit point of E is a real number p such that
    for any positive real number eps
    there exists e \in E such that 0 < d(e,p) < eps.



Theorem 5_3a.
  Let f be a real map such that f is defined on [x|y].
  Let g be a real map such that g is defined on [x|y].
  Let p be an element of (x|y).
  Assume that f is differentiable at p.
  Assume that g is differentiable at p.
  Then f++g is differentiable at p and
  D(f++g,p) = D(f,p) + D(g,p).