# MEAN VALUE THEOREMS

[prove off]
[check off]
[read preliminaries.ftl]
[read real-analysis/numbers.ftl]
[read real-analysis/Chapter5/mean_value_theorems_pre.ftl]
[timelimit 30]

[prove on]
[check on]


# NOTATION
Let x,y denote real numbers.
Let eps, del denote positive real numbers.


# LOCAL MINIMA AND MAXIMA
Definition 5_7a.
  Let f be a real map.
  A local minima of f is an element p of Dom(f) such that there exists del such that
    for any t \in Dom(f) if d(t,p)<del then f(t)>=f(p).


Definition 5_7b.
  Let f be a real map.
  A local maxima of f is an element p of Dom(f) such that there exists del such that
    for any t \in Dom(f) if d(t,p)<del then f(t)<=f(p).


Lemma 5_8_2a.
  Let f be a real map.
  Let p be a real number such that p is a limit point of Dom(f).
  Let q be a real number such that lim(f,p)=q.
  Suppose for every t \in Dom(f) f(t)<=0. Then q<=0.
Proof.
  Suppose the contrary.
  Then q is a positive real number.
  Let us show that there exists del such that for any t \in Dom(f) if 0<d(t,p)<del then d(f(t),q)<q.
    lim(f,p) = q iff for any eps there exists del such that
      for any t \in Dom(f) if 0<d(t,p)<del then d(f(t),q)<eps (by LimitAxiom).
    Therefore the thesis. Indeed lim(f,p) = q and q is a positive real number.
  End.
  Take del such that for any t \in Dom(f)
    if 0<d(t,p)<del then d(f(t),q)<q.
  Take t \in Dom(f) such that 0<d(t,p)<del (by 5_8_1).
  Indeed Dom(f) is a subset of Real and p is a limit point of Dom(f) and del is a positive real number.
  Then d(f(t),q)<q.
  Then q-q < f(t) (by d4).
  Then 0 < f(t).
  Contradiction.
QED.

Lemma 5_8_2b.
  Let f be a real map.
  Let p be a real number such that p is a limit point of Dom(f).
  Let q be a real number such that lim(f,p)=q.
  Let c be a real number.
  Suppose for any t \in Dom(f) f(t)>=0. Then q>=0.
Proof.
  Suppose the contrary.
  Then -q is a positive real number.
  Let us show that there exists del such that for any t \in Dom(f) if 0<d(t,p)<del then d(f(t),q)<-q.
    lim(f,p) = q iff for any eps there exists del such that
      for any t \in Dom(f) if 0<d(t,p)<del then d(f(t),q)<eps (by LimitAxiom).
    Therefore the thesis. Indeed lim(f,p) = q and -q is a positive real number.
  End.
  Take del such that for any t \in Dom(f)
    if 0<d(t,p)<del then d(f(t),q)<-q.
  Take t \in Dom(f) such that 0<d(t,p)<del (by 5_8_1).
  Indeed Dom(f) is a subset of Real and p is a limit point of Dom(f) and del is a positive real number.
  Then d(f(t),q)<-q.
  Then f(t) < q+(-q) (by d4).
  Then f(t) < 0.
  Contradiction.
QED.


Lemma 5_8_3a.
  Let c be a real number such that c<0.
  Then 1/c < 0.

Lemma 5_8_3b.
  Let c be a real number such that c>0.
  Then 1/c > 0.

Lemma 5_8_4.
  Let a,b,c be positive real numbers.
  Then there exists a positive real number d such that
  d<a and d<b and d<c.
Proof.
  Case a <= b and a <= c.
    There exists positive real number d such that d < a.
  End.
  Case b <= a and b <= c.
    There exists positive real number d such that d < b.
  End.
  Case c <= b and c <= a.
    There exists positive real number d such that d < c.
  End.
QED.


Theorem 5_8a.
  Let f be a real map that is defined on [x|y].
  Let p be an element of (x|y).
  If f is differentiable at p and p is a local minima of f
  then D(f,p)=0.
Proof.
  Assume f is differentiable at p and p is a local minima of f.

  Let us show that there exists del such that x<p-del and p+del<y
      and for any t \in [x|y] if d(t,p)<del then f(t)>=f(p).
    Take positive real number del' such that for any t \in [x|y] if d(t,p)<del' then f(t)>=f(p) (by 5_7a).
    Indeed p is a local minima of f.
    Then p-x, y-p and del' are positive real numbers. Indeed p>x and y>p.
    Take del such that del<p-x and del<y-p and del<del' (by 5_8_4).
    del+x<p. Indeed (p-x)+x = p+(-x+x) = p.
    Then x<p-del. Indeed (del+x)-del = (x+del)-del = x+(del-del) = x.
    p+del<y. Indeed del+p = p+del.
    Let us show that for any t \in [x|y] if d(t,p)<del then f(t)>=f(p).
      Assume t \in [x|y] and d(t,p)<del.
      Then d(t,p)<del'. Indeed del<del'.
      Then f(t)>=f(p).
    End.
  End.
  Take del such that x<p-del and p+del<y and for any t \in [x|y] if d(t,p)<del then f(t)>=f(p).
  
  
  Take real number d such that D(f,p)=d.
  DQ(f,p) is a real map that is defined on [x|y]\\{p}.

  # calculationg D(f,p) from below:
  Let us show that d<=0.
    Let us show that (p-del|p) is a subset of Dom(DQ(f,p)).
      Assume t \in (p-del|p).
      Then p-del < t < p (by OpenInterval).
      Then x < t and t < y and t != p. Indeed x < p-del and p < y.
      Then t \in Dom(DQ(f,p)). Indeed Dom(DQ(f,p)) = [x|y]\\{p}.
    End.
    # res1: restriction of DQ(f,p) to numbers <p.
    Define res1(t) = DQ(f,p)(t) for t in (p-del|p).
    Then res1 is a real map that is defined on (p-del|p).
    Indeed for any t \in (p-del|p) DQ(f,p)(t) is a real number.
    Then p is a limit point of Dom(res1). Indeed Dom(res1) = (p-del|p) and p \in [p-del|p].
    Let us show that lim(res1,p)=d.
      DQ(f,p), res1 are real map such that Dom(res1) is a subset of Dom(DQ(f,p)).
      p is a limit point of Dom(res1).
      For any t \in Dom(res1) res1(t) = DQ(f,p)(t).
      lim(DQ(f,p),p)=d.
      Then the thesis (by LimitOfRestrictedFunction).
    End.
    Let us show that for any t \in (p-del|p) res1(t)<=0.
      Assume t \in (p-del|p).
      Then p-del < t < p+del.
      Then d(t,p)<del.
      f(t)-f(p) >= 0. Indeed f(t)>=f(p).
      1/(t-p) < 0 (by 5_8_3a). Indeed t-p<0.
      Then (f(t)-f(p)) // (t-p) <= 0*0 = 0.
      res1(t) = (f(t)-f(p)) // (t-p) (by DifferenceQuotient). Indeed res1(t) = DQ(f,p)(t).
      Then res1(t) <= 0.
    End.
    Let us show that if for every t \in Dom(res1) res1(t)<=0 then d<=0.
      res1 is a real map.
      p is a real number such that p is a limit point of Dom(res1).
      d is a real number such that lim(res1,p)=d.
      Therefore the thesis (by 5_8_2a).
    End.
  End.

  # calculating D(f,p) from above:
  Let us show that d>=0.
    Let us show that (p|p+del) is a subset of Dom(DQ(f,p)).
      Assume t \in (p|p+del).
      Then p < t < p+del (by OpenInterval).
      Then x < t and t < y and t != p. Indeed x < p and p+del < y.
      Then t \in Dom(DQ(f,p)). Indeed Dom(DQ(f,p)) = [x|y]\\{p}.
    End.
    # res2: restriction of DQ(f,p) to numbers >p.
    Define res2(t) = DQ(f,p)(t) for t in (p|p+del).
    Then res2 is a real map that is defined on (p|p+del).
    Indeed for any t \in (p|p+del) DQ(f,p)(t) is a real number.
    Then p is a limit point of Dom(res2). Indeed Dom(res2) = (p|p+del) and p \in [p|p+del].
    Let us show that lim(res2,p)=d.
      DQ(f,p), res2 are real map such that Dom(res2) is a subset of Dom(DQ(f,p)).
      p is a limit point of Dom(res2).
      For any t \in Dom(res2) res2(t) = DQ(f,p)(t).
      lim(DQ(f,p),p)=d.
      Then the thesis (by LimitOfRestrictedFunction).
    End.
    Let us show that for any t \in (p|p+del) res2(t)>=0.
      Assume t \in (p|p+del).
      Then p-del < t < p+del.
      Then d(t,p)<del.
      f(t)-f(p) >= 0. Indeed f(t)>=f(p).
      1/(t-p) > 0 (by 5_8_3b). Indeed t-p>0.
      Then (f(t)-f(p)) // (t-p) >= 0*0 = 0.
      res2(t) = (f(t)-f(p)) // (t-p) (by DifferenceQuotient). Indeed res2(t) = DQ(f,p)(t).
      Then res2(t) >= 0.
    End.
    Let us show that if for any t \in Dom(res2) res2(t)>=0 then d>=0.
      res2 is a real map.
      p is a real number such that p is a limit point of Dom(res2).
      d is a real number such that lim(res2,p)=d.
      0 is a real number.
      Therefore the thesis (by 5_8_2b).
    End.
  End.
QED.


Theorem 5_8b.
  Let f be a real map that is defined on [x|y].
  Let p be an element of (x|y).
  If f is differentiable at p and p is a local maxima of f
  then D(f,p)=0.
Proof.
  Assume f is differentiable at p and p is a local maxima of f.
  Let us show that there exists del such that x<p-del and p+del<y
      and for any t \in [x|y] if d(t,p)<del then f(t)<=f(p).
    Take positive real number del' such that for any t \in [x|y] if d(t,p)<del' then f(t)<=f(p) (by 5_7a).
    Indeed p is a local maxima of f.
    Then p-x, y-p and del' are positive real numbers. Indeed p>x and y>p.
    Take del such that del<p-x and del<y-p and del<del' (by 5_8_4).
    del+x<p. Indeed (p-x)+x = p+(-x+x) = p.
    Then x<p-del. Indeed (del+x)-del = (x+del)-del = x+(del-del) = x.
    p+del<y. Indeed del+p = p+del.
    Let us show that for any t \in [x|y] if d(t,p)<del then f(t)<=f(p).
      Assume t \in [x|y] and d(t,p)<del.
      Then d(t,p)<del'. Indeed del<del'.
      Then f(t)<=f(p).
    End.
  End.
  Take del such that x<p-del and p+del<y and for any t \in [x|y] if d(t,p)<del then f(t)<=f(p).
  
  Take real number d such that D(f,p)=d.
  DQ(f,p) is a real map that is defined on [x|y]\\{p}.

  Let us show that d>=0.
    Let us show that (p-del|p) is a subset of Dom(DQ(f,p)).
      Assume t \in (p-del|p).
      Then p-del < t < p (by OpenInterval).
      Then x < t and t < y and t != p. Indeed x < p-del and p < y.
      Then t \in Dom(DQ(f,p)). Indeed Dom(DQ(f,p)) = [x|y]\\{p}.
    End.
    # res1: restriction of DQ(f,p) to numbers <p.
    Define res1(t) = DQ(f,p)(t) for t in (p-del|p).
    Then res1 is a real map. Indeed DQ(f,p) is a real map.
    Indeed for any t \in (p-del|p) DQ(f,p)(t) is a real number.
    Then p is a limit point of Dom(res1). Indeed Dom(res1) = (p-del|p) and p \in [p-del|p].
    Let us show that lim(res1,p)=d.
      DQ(f,p), res1 are real map such that Dom(res1) is a subset of Dom(DQ(f,p)).
      p is a limit point of Dom(res1).
      For any t \in Dom(res1) res1(t) = DQ(f,p)(t).
      lim(DQ(f,p),p)=d.
      Then the thesis (by LimitOfRestrictedFunction).
    End.
    Let us show that for any t \in (p-del|p) res1(t)>=0.
      Assume t \in (p-del|p).
      Then p-del < t < p+del.
      Then d(t,p)<del.
      f(t)-f(p) <= 0. Indeed f(t)<=f(p).
      1/(t-p) < 0 (by 5_8_3a). Indeed t-p<0.
      Then (f(t)-f(p))*(1/(t-p)) >= 0*0 = 0.
      res1(t) = (f(t)-f(p))*(1/(t-p)) (by DifferenceQuotient). Indeed res1(t) = DQ(f,p)(t).
      Then res1(t) >= 0.
    End.
    Let us show that if for every t \in Dom(res1) res1(t)>=0 then d>=0.
      res1 is a real map.
      p is a real number such that p is a limit point of Dom(res1).
      d is a real number such that lim(res1,p)=d.
      Therefore the thesis (by 5_8_2b).
    End.
  End.
  Let us show that d<=0.
    Let us show that (p|p+del) is a subset of Dom(DQ(f,p)).
      Assume t \in (p|p+del).
      Then p < t < p+del (by OpenInterval).
      Then x < t and t < y and t != p. Indeed x < p and p+del < y.
      Then t \in Dom(DQ(f,p)). Indeed Dom(DQ(f,p)) = [x|y]\\{p}.
    End.
    # res2: restriction of DQ(f,p) to numbers >p.
    Define res2(t) = DQ(f,p)(t) for t in (p|p+del).
    Then res2 is a real map that is defined on (p|p+del).
    Indeed for any t \in (p|p+del) DQ(f,p)(t) is a real number.
    Then p is a limit point of Dom(res2). Indeed Dom(res2) = (p|p+del) and p \in [p|p+del].
    Let us show that lim(res2,p)=d.
      DQ(f,p), res2 are real map such that Dom(res2) is a subset of Dom(DQ(f,p)).
      p is a limit point of Dom(res2).
      For any t \in Dom(res2) res2(t) = DQ(f,p)(t).
      lim(DQ(f,p),p)=d.
      Then the thesis (by LimitOfRestrictedFunction).
    End.
    Let us show that for any t \in (p|p+del) res2(t)<=0.
      Assume t \in (p|p+del).
      Then p-del < t < p+del.
      Then d(t,p)<del.
      f(t)-f(p) <= 0. Indeed f(t)<=f(p).
      1/(t-p) > 0 (by 5_8_3b). Indeed t-p>0.
      Then (f(t)-f(p))*(1/(t-p)) <= 0*0 = 0.
      res2(t) = (f(t)-f(p))*(1/(t-p)) (by DifferenceQuotient). Indeed res2(t) = DQ(f,p)(t).
      Then res2(t) <= 0.
    End.
    Let us show that if for any t \in Dom(res2) res2(t)<=0 then d<=0.
      res2 is a real map.
      p is a real number such that p is a limit point of Dom(res2).
      d is a real number such that lim(res2,p)=d.
      0 is a real number.
      Therefore the thesis (by 5_8_2a).
    End.
  End.
QED.


Theorem 5_9.
  Let x < y.
  Let f,g be real map that are defined on [x|y].
  Let f be continuous and differentiable on (x|y).
  Let g be continuous and differentiable on (x|y).
  Then there exists p \in (x|y) such that
    (f(y)-f(x))*D(g,p) = (g(y)-g(x))*D(f,p).
Proof.
  # function h
  Take c = (f(y)-f(x)).
  Take d = (g(x)-g(y)).
  Take h = (c~g)++(d~f).
  Then h is a real map that is defined on [x|y].
  
  # derivative of h
  Let us show that for any t \in (x|y) D(h,t) = ((f(y)-f(x))*D(g,t)) + ((g(x)-g(y))*D(f,t)).
    Suppose t \in (x|y).
    Let us show that D(c~g,t) = c*D(g,t).
      t is a limit point of Dom(g).
      g is a real map that is defined on [x|y].
      c is a real number.
      t is an element of (x|y).
      g is differentiable at t. Indeed g is differentiable on (x|y).
      Then the thesis (by DerivativeOfScaledFunction).
    End.
    Let us show that D(d~f,t) = d*D(f,t).
      t is a limit point of Dom(f).
      f is a real map that is defined on [x|y].
      d is a real number.
      t is an element of (x|y).
      f is differentiable at t. Indeed f is differentiable on (x|y).
      Then the thesis (by DerivativeOfScaledFunction).
    End.
    Let us show that D(h,t) = D(c~g,t) + D(d~f,t).
      c~g is a real map that is defined on [x|y].
      d~f is a real map that is defined on [x|y].
      t is an element of (x|y).
      c~g is differentiable at t. Indeed D(c~g,t) = c*D(g,t) (by DerivativeOfScaledFunction).
      d~f is differentiable at t. Indeed D(d~f,t) = d*D(f,t) (by DerivativeOfScaledFunction).
      Then the thesis (by 5_3a).
    End.
  End.

  # h is continuous.
  Let us show that h is continuous.
    Suppose t \in Dom(h).
    Dom(c~g) = Dom(d~f).
    c~g is continuous at t (by ContinuityOfScaledFunction).
    Indeed g is continuous at t and t is a limit point of Dom(g).
    d~f is continuous at t (by ContinuityOfScaledFunction).
    Indeed f is continuous at t and t is a limit point of Dom(f).
    t is a limit point of Dom(c~g).
    h is continuous at t (by 4_9a). Indeed h = (c~g)++(d~f).
  End.

  # h is differentiable.
  Let us show that h is differentiable on (x|y).
    Suppose t \in (x|y).
    Then D(h,t) = ((f(y)-f(x))*D(g,t)) + ((g(x)-g(y))*D(f,t)).
    Then h is differentiable at t.
  End.

  # it's enough to show D(h,p) = 0.
  Let us show that if there exists p \in (x|y) such that D(h,p)=0 then the thesis.
    Assume that there exists p \in (x|y) such that D(h,p) = 0.
    Take p \in (x|y) such that D(h,p) = 0.
    Then D(h,p) = ((f(y)-f(x))*D(g,p)) + ((g(x)-g(y))*D(f,p)).
    Then ((f(y)-f(x))*D(g,p)) + ((g(x)-g(y))*D(f,p)) = 0.
    ((f(y)-f(x))*D(g,p)) = -((g(x)-g(y))*D(f,p)).
    -((g(x)-g(y))*D(f,p)) = -(g(x)-g(y))*D(f,p).
    -(g(x)-g(y))*D(f,p) = (-g(x)+g(y))*D(f,p).
    (-g(x)+g(y))*D(f,p) = (g(y)-g(x))*D(f,p).
    Then (f(y)-f(x))*D(g,p) = (g(y)-g(x))*D(f,p).
  End.

  # h(x) = h(y).
  x \in [x|y] and y \in [x|y].
  Let us show that h(x) = h(y).
    Let us show that for any t \in [x|y] h(t) = ((f(y)*g(t))-(f(x)*g(t))) + ((g(x)*f(t))-(g(y)*f(t))).
      Suppose t \in [x|y].
      h(t) = (c~g)(t) + (d~f)(t) (by Addition).
      (c~g)(t) = c * g(t) (by Scaling).
      (d~f)(t) = d * f(t) (by Scaling).
      Then h(t) = (c*g(t)) + (d*f(t)).
      c = f(y)-f(x).
      d = g(x)-g(y).
      Then c * g(t) = ((f(y)-f(x))*g(t)) = (f(y)*g(t)) - (f(x)*g(t)).
      Then d * f(t) = ((g(x)-g(y))*f(t)) = (g(x)*f(t)) - (g(y)*f(t)).
      Then h(t) = ((f(y)*g(t))-(f(x)*g(t))) + ((g(x)*f(t))-(g(y)*f(t))).
    End.
    Let us show that h(x) = (f(y)*g(x))-(g(y)*f(x)).
      h(x) = ((f(y)*g(x))-(f(x)*g(x))) + ((g(x)*f(x))-(g(y)*f(x))).
      ((f(y)*g(x))-(f(x)*g(x))) + ((g(x)*f(x))-(g(y)*f(x))) = (((f(y)*g(x))-(f(x)*g(x))) + (g(x)*f(x))) - (g(y)*f(x)).
      (((f(y)*g(x))-(f(x)*g(x))) + (g(x)*f(x))) - (g(y)*f(x)) = ((f(y)*g(x)) + (-(f(x)*g(x))+(g(x)*f(x)))) - (g(y)*f(x)).
      ((f(y)*g(x)) + (-(f(x)*g(x))+(g(x)*f(x)))) - (g(y)*f(x)) = ((f(y)*g(x)) + (-(g(x)*f(x))+(g(x)*f(x)))) - (g(y)*f(x)).
      ((f(y)*g(x)) + (-(g(x)*f(x))+(g(x)*f(x)))) - (g(y)*f(x)) = (f(y)*g(x)) - (g(y)*f(x)).
    End.  
    Let us show that h(y) = -(f(x)*g(y))+(g(x)*f(y)).
      h(y) = ((f(y)*g(y))-(f(x)*g(y))) + ((g(x)*f(y))-(g(y)*f(y))).
      ((f(y)*g(y))-(f(x)*g(y))) + ((g(x)*f(y))-(g(y)*f(y))) = (-(f(x)*g(y))+(f(y)*g(y))) + ((g(x)*f(y))-(g(y)*f(y))).
      (-(f(x)*g(y))+(f(y)*g(y))) + ((g(x)*f(y))-(g(y)*f(y))) = (-(f(x)*g(y))+(f(y)*g(y))) + (-(g(y)*f(y))+(g(x)*f(y))).
      (-(f(x)*g(y))+(f(y)*g(y))) + (-(g(y)*f(y))+(g(x)*f(y))) = ((-(f(x)*g(y))+(f(y)*g(y))) - (g(y)*f(y))) + (g(x)*f(y)).
      ((-(f(x)*g(y))+(f(y)*g(y))) - (g(y)*f(y))) + (g(x)*f(y)) = (-(f(x)*g(y)) + ((f(y)*g(y)) - (g(y)*f(y)))) + (g(x)*f(y)).
      (-(f(x)*g(y)) + ((f(y)*g(y)) - (g(y)*f(y)))) + (g(x)*f(y)) = (-(f(x)*g(y)) + ((g(y)*f(y)) - (g(y)*f(y)))) + (g(x)*f(y)).
      (-(f(x)*g(y)) + ((g(y)*f(y)) - (g(y)*f(y)))) + (g(x)*f(y)) = -(f(x)*g(y)) + (g(x)*f(y)).
    End.
    Then h(y) = -(f(x)*g(y))+(g(x)*f(y)).
    -(f(x)*g(y))+(g(x)*f(y)) = (g(x)*f(y))-(f(x)*g(y)).
    (g(x)*f(y))-(f(x)*g(y)) = (f(y)*g(x))-(f(x)*g(y)).
    (f(y)*g(x))-(f(x)*g(y)) = (f(y)*g(x))-(g(y)*f(x)).
  End.

  # 3 cases
  (For any t \in (x|y) h(t) = h(x)) or (there exists t \in (x|y) such that h(t) > h(x))
    or (there exists t \in (x|y) such that h(t) < h(x)).
    
  # Case 1: h is constant
  Case for any t \in (x|y) h(t) = h(x).
    Then for any t \in [x|y] h(t) = h(x). Indeed h(y) = h(x).
    Take p \in (x|y).
    Let us show that D(h,p) = 0.
      h is a real map that is defined on [x|y].
      h(x) is a real number such that for any t \in [x|y] h(t) = h(x).
      p is an element of (x|y).
      Then h is differentiable at p and D(h,p) = 0 (by DerivativeOfConstantFunction).
    End.
    Therefore the thesis. Indeed there exists t \in (x|y) such that D(h,t)=0.
  End.

  # Case 2: h has a maxima in (x|y).
  Case there exists t \in (x|y) such that h(t) > h(x).
    Let us show that there exists p \in (x|y) such that p is a local maxima of h.
      h is continuous.
      Dom(h) is nonempty.
      Dom(h) is compact (by Compactness). Indeed Dom(h) = [x|y].
      Then there exists p \in Dom(h) such that
      for any t \in Dom(h) h(t) <= h(p) (by 4_16a).
      Take p \in Dom(h) such that for any t \in Dom(h) h(t) <= h(p).
      Take q \in (x|y) such that h(q) > h(x).
      Let us show that p \in (x|y).
        p \in [x|y].
        h(q) <= h(p). Indeed p,q \in Dom(h).
        Then h(x) < h(p). Indeed h(x) < h(q) <= h(p).
        Then h(p) != h(x).
        Then p != x.
        h(p) != h(x). Indeed h(p) != h(x) = h(y).
        Then p != y.
      End.
      Let us show that p is a local maxima of h.
        1 is a positive real number.
        Let us show that for any t \in Dom(h) if d(t,p)<1 then h(t)<=h(p).
          Assume t \in Dom(h).
          Then h(t)<=h(p).
        End.
        Therefore the thesis (by 5_7b).
      End.
    End.
    Take p \in (x|y) such that p is a local maxima of h.
    p is a limit point of Dom(h).
    Let us show that D(h,p)=0.
      h is a real map that is defined on [x|y].
      p is an element of (x|y).
      h is differentiable at p and p is a local maxima of h. Indeed h is differentiable on (x|y).
      Therefore the thesis (by 5_8b).
    End.
    Therefore the thesis. Indeed there exists t \in (x|y) such that D(h,t)=0.
  End.

  # Case 3: h has a minima in (x|y).
  Case there exists t \in (x|y) such that h(t) < h(x).
    Let us show that there exists p \in (x|y) such that p is a local minima of h.
      h is continuous.
      Dom(h) is nonempty.
      Dom(h) is compact (by Compactness). Indeed Dom(h) = [x|y].
      Then there exists  p \in Dom(h) such that
      for any t \in Dom(h) h(t) >= h(p) (by 4_16b).
      Take p \in Dom(h) such that for any t \in Dom(h) h(t) >= h(p).
      Take q \in (x|y) such that h(q) < h(x).
      Let us show that p \in (x|y).
        p \in [x|y].
        h(q) >= h(p). Indeed p,q \in Dom(h).
        Then h(x) > h(p). Indeed h(x) > h(q) >= h(p).
        Then h(p) != h(x).
        Then p != x.
        h(p) != h(x). Indeed h(p) != h(x) = h(y).
        Then p != y.
      End.
      Let us show that p is a local minima of h.
        1 is a positive real number.
        Let us show that for any t \in Dom(h) if d(t,p)<1 then h(t)>=h(p).
          Assume t \in Dom(h).
          Then h(t)>=h(p).
        End.
        Therefore the thesis (by 5_7a).
      End.
    End.
    Take p \in (x|y) such that p is a local minima of h.
    p is a limit point of Dom(h).
    Let us show that D(h,p)=0.
      h is a real map that is defined on [x|y].
      p is an element of (x|y).
      h is differentiable at p and p is a local minima of h. Indeed h is differentiable on (x|y).
      Therefore the thesis (by 5_8a).
    End.
    Therefore the thesis. Indeed there exists t \in (x|y) such that D(h,t)=0.
  End.
QED.