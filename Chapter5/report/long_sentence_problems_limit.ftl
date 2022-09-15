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

[prove on]
[check on]

Definition.
  Let f be a real map.
  Let p be a limit point of Dom(f).
  Let q be a real number.
  lim(f,p) = q iff for any positive real number eps there exists a positive real number del
    such that for any t \in Dom(f) if d(t,p)<del then d(f(t),q)<eps.

Lemma.
  Let f be a real map.
  Let p be a limit point of Dom(f).
  Let q be a real number.
  lim(f,p) = q iff for any positive real number eps there exists a positive real number del
    such that for any t \in Dom(f) if d(t,p)<del then d(f(t),q)<eps.