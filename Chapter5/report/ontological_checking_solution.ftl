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

[prove on]
[check on]

Lemma.
  Let f be a real map.
  For any t \in Dom(f) f(t) = (f(t) - (f(t) + f(t))) + ((1+1)*f(t)).
Proof.
  Assume t \in Dom(f).
  Take ft = f(t). ft is a real number.
  Then (ft - (ft + ft)) + ((1+1)*ft) = (ft + (-ft - ft)) + ((1+1)*ft).
  (ft + (-ft - ft)) + ((1+1)*ft) = ((ft - ft) - ft) + ((1+1)*ft).
  ((ft - ft) - ft) + ((1+1)*ft) = ft.
QED.