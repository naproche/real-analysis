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
Let a,b, A,B denote real numbers.


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
  Let p be a limit point of Dom(f).
  Suppose for every t \in Dom(f) f(t) <= 0.
  If lim(f,p) exists then lim(f,p) <= 0.
Proof.
  Assume that lim(f,p) exists.
  Take real number A such that lim(f,p) = A (by LimitExists).
  Indeed f is a real map and p is a limit point of Dom(f).
  Suppose the contrary.
  Then A > 0.

  # Take del such that...
  Then for any positive real number eps A is limit of f at p wrt eps.
  Then A is limit of f at p wrt A. Indeed A is a positive real number.
  Take positive del such that A is limit of f at p wrt A and del (by LimitWrt).
  Then for any t \in Dom(f) if 0<d(t,p)<del then d(f(t),A)<A (by LimitWrtAnd).

  Take t \in Dom(f) such that 0<d(t,p)<del (by LimitPoint).
  Indeed p is a limit point of Dom(f) and del is a positive real number.
  Take ft = f(t). ft is a real number.
  Then d(ft,A)<A.
  Then A-A < ft (by d4).
  Then 0 < ft.
  Contradiction.
QED.

Lemma 5_8_2b.
  Let f be a real map.
  Let p be a limit point of Dom(f).
  Suppose for every t \in Dom(f) f(t) >= 0.
  If lim(f,p) exists then lim(f,p) >= 0.
Proof.
  Assume that lim(f,p) exists.
  Take real number A such that lim(f,p) = A (by LimitExists).
  Suppose the contrary.
  Then -A is a positive real number.

  # Take del such that...
  For any positive real number eps A is limit of f at p wrt eps.
  Then A is limit of f at p wrt -A. Indeed -A is a positive real number.
  Take positive del such that A is limit of f at p wrt -A and del (by LimitWrt).
  Then for any t \in Dom(f) if 0<d(t,p)<del then d(f(t),A)<-A (by LimitWrtAnd).

  Take t \in Dom(f) such that 0<d(t,p)<del (by LimitPoint).
  Indeed Dom(f) is a subset of Real
    and p is a limit point of Dom(f)
    and del is a positive real number.
  Take ft = f(t). ft is a real number.
  Then d(ft,A)<-A.
  Then ft < A+(-A) (by d4).
  Then ft < 0.
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

Lemma 5_8_5.
  Let a,b be real numbers.
  Suppose a < b.
  Then b-a is a positive real number.
Proof.
  a-a < b-a.
  a-a = 0 (by 1_12_A5).
  Then 0 < b-a.
QED.

Theorem 5_8a.
  Let f be a real map that is defined on [x|y].
  Let p be an element of (x|y).
  If f is differentiable at p and p is a local minima of f
  then D(f,p) = 0.
Proof.
  Assume f is differentiable at p and p is a local minima of f.
  Take fp = f(p). Then fp is a real number.
  Let us show that there exists del such that x<p-del and p+del<y
      and for any t \in [x|y] if d(t,p)<del then f(t)>=fp.
    Take positive real number del' such that
    for any t \in [x|y] if d(t,p)<del' then f(t)>=fp (by 5_7a).
    Indeed p is a local minima of f.
    Then p-x, y-p and del' are positive real numbers. Indeed p>x and y>p.
    Take del such that del<p-x and del<y-p and del<del' (by 5_8_4).
    del+x<p. Indeed (p-x)+x = p+(-x+x) = p.
    Then x<p-del. Indeed (del+x)-del = (x+del)-del = x+(del-del) = x.
    p+del<y. Indeed del+p = p+del.
    Let us show that for any t \in [x|y] if d(t,p)<del then f(t)>=f(p).
      Assume t \in [x|y] and d(t,p)<del.
      Then d(t,p)<del'. Indeed del<del'.
      Then f(t)>=fp.
    End.
  End.
  Take del such that x<p-del and p+del<y and for any t \in [x|y] if d(t,p)<del then f(t)>=fp.
  
  Take real number d such that D(f,p) = d.
  DQ(f,p) is a real map that is defined on [x|y]\\{p}.

  # calculating D(f,p) from below:
  Let us show that d<=0.
    Let us show that (p-del|p) is a subset of Dom(DQ(f,p)).
      Assume t \in (p-del|p).
      Then p-del < t < p (by OpenInterval).
      Then x < t and t < y and t != p. Indeed x < p-del and p < y.
      Then t \in Dom(DQ(f,p)). Indeed Dom(DQ(f,p)) = [x|y]\\{p}.
    End.
    # res1: restriction of DQ(f,p) to numbers <p.
    Define res1(t) = DQ(f,p)(t) for t in (p-del|p).
    Then res1 is a restriction of DQ(f,p).
    Then p is a limit point of Dom(res1). Indeed Dom(res1) = (p-del|p) and p \in [p-del|p].
    Let us show that if lim(DQ(f,p),p) exists then lim(res1,p) = lim(DQ(f,p),p).
      DQ(f,p) is a real map.
      res1 is a restriction of DQ(f,p).
      p is a limit point of Dom(res1).
      Then the thesis (by LimitOfRestrictedFunction).
    End.
    Therefore lim(res1,p)=d. Indeed for any t \in Dom(res1) res1(t) = DQ(f,p)(t).
    Let us show that for any t \in (p-del|p) res1(t)<=0.
      Assume t \in (p-del|p).
      Take ft = f(t). Then ft is a real number. Indeed t \in Dom(f).
      Then p-del < t < p (by OpenInterval).
      0 < del.
      Then p < p + del.
      Then t < p + del (by 1_5_ii). Indeed t < p.
      Then d(t,p)<del (by d4).
      Let us show that ft-fp >= 0.
        t \in [x|y].
        d(t,p)<del.
        Then ft >= fp.
        Then ft-fp >= fp-fp.
        fp-fp = 0 (by 1_12_A5).
        Therefore the thesis.
      End.
      Take inv = 1/(t-p). Then inv is a real number.
      inv < 0 (by 5_8_3a). Indeed t-p<0.
      Then 0 * inv >= (ft-fp) * inv (by 1_18_cc). Indeed 0 <= ft-fp.
      0 * inv = 0 (by 1_16_a).
      Then (ft-fp) * inv <= 0.
      res1(t) = (ft-fp) * inv (by DifferenceQuotient). Indeed res1(t) = DQ(f,p)(t).
      Then res1(t) <= 0.
    End.
    Let us show that if lim(res1,p) exists then d <= 0.
      res1 is a real map.
      p is a limit point of Dom(res1).
      For every t \in Dom(res1) res1(t) <= 0.
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
    Then res2 is a restriction of DQ(f,p).
    Then p is a limit point of Dom(res2). Indeed Dom(res2) = (p|p+del) and p \in [p|p+del].
    Let us show that if lim(DQ(f,p),p) exists then lim(res2,p) = lim(DQ(f,p),p).
      DQ(f,p) is a real map.
      res2 is a restriction of DQ(f,p).
      p is a limit point of Dom(res2).
      Then the thesis (by LimitOfRestrictedFunction).
    End.
    Therefore lim(res2,p) = d.
    Let us show that for any t \in (p|p+del) res2(t)>=0.
      Assume t \in (p|p+del).
      Take ft = f(t). Then ft is a real number. Indeed t \in Dom(f).
      Then p < t < p+del (by OpenInterval).
      -del < 0.
      Then p - del < p + 0.
      p + 0 = p (by 1_12_A4).
      Then p-del < t (by 1_5_ii). Indeed p-del < p and p < t.
      Then d(t,p)<del (by d4).
      Let us show that ft-fp >= 0.
          t \in [x|y].
          d(t,p)<del.
          Then ft >= fp.
          Then ft-fp >= fp-fp.
          fp-fp = 0 (by 1_12_A5).
          Therefore the thesis.
      End.
      Take inv = 1/(t-p). Then inv is a real number.
      inv > 0 (by 5_8_3b). Indeed t-p>0.
      Then (ft-fp) * inv >= 0 * inv (by 1_18_bb).
      0 * inv = 0 (by 1_16_a).
      Then (ft-fp) * inv >= 0.
      res2(t) = (ft-fp) * inv (by DifferenceQuotient). Indeed res2(t) = DQ(f,p)(t).
      Then res2(t) >= 0.
    End.
    Let us show that if lim(res2,p) exists then d >= 0.
      res2 is a real map.
      p is a limit point of Dom(res2).
      For every t \in Dom(res2) res2(t) >= 0.
      Therefore the thesis (by 5_8_2b).
    End.
  End.
QED.


Theorem 5_8b.
  Let f be a real map that is defined on [x|y].
  Let p be an element of (x|y).
  If f is differentiable at p and p is a local maxima of f
  then D(f,p) = 0.
Proof.
  Assume f is differentiable at p and p is a local maxima of f.
  Take fp = f(p). Then fp is a real number.
  Let us show that there exists del such that x<p-del and p+del<y
      and for any t \in [x|y] if d(t,p)<del then f(t)<=fp.
    Take positive real number del' such that
    for any t \in [x|y] if d(t,p)<del' then f(t)<=fp (by 5_7a).
    Indeed p is a local maxima of f.
    Then p-x, y-p and del' are positive real numbers. Indeed p>x and y>p.
    Take del such that del<p-x and del<y-p and del<del' (by 5_8_4).
    del+x<p. Indeed (p-x)+x = p+(-x+x) = p.
    Then x<p-del. Indeed (del+x)-del = (x+del)-del = x+(del-del) = x.
    p+del<y. Indeed del+p = p+del.
    Let us show that for any t \in [x|y] if d(t,p)<del then f(t)<=fp.
      Assume t \in [x|y] and d(t,p)<del.
      Then d(t,p)<del'. Indeed del<del'.
      Then f(t)<=fp.
    End.
  End.
  Take del such that x<p-del and p+del<y and for any t \in [x|y] if d(t,p)<del then f(t)<=fp.
  
  Take real number d such that D(f,p) = d.
  DQ(f,p) is a real map that is defined on [x|y]\\{p}.

  # calculating D(f,p) from below:
  Let us show that d>=0.
    Let us show that (p-del|p) is a subset of Dom(DQ(f,p)).
      Assume t \in (p-del|p).
      Then p-del < t < p (by OpenInterval).
      Then x < t and t < y and t != p. Indeed x < p-del and p < y.
      Then t \in Dom(DQ(f,p)). Indeed Dom(DQ(f,p)) = [x|y]\\{p}.
    End.
    # res1: restriction of DQ(f,p) to numbers <p.
    Define res1(t) = DQ(f,p)(t) for t in (p-del|p).
    Then res1 is a restriction of DQ(f,p).
    Then p is a limit point of Dom(res1). Indeed Dom(res1) = (p-del|p) and p \in [p-del|p].
    Let us show that if lim(DQ(f,p),p) exists then lim(res1,p) = lim(DQ(f,p),p).
      DQ(f,p) is a real map.
      res1 is a restriction of DQ(f,p).
      p is a limit point of Dom(res1).
      Then the thesis (by LimitOfRestrictedFunction).
    End.
    Therefore lim(res1,p) = d.
    Let us show that for any t \in (p-del|p) res1(t)>=0.
      Assume t \in (p-del|p).
      Take ft = f(t). Then ft is a real number. Indeed t \in Dom(f).
      Then p-del < t < p (by OpenInterval).
      0 < del.
      Then p < p+del.
      Then t < p+del (by 1_5_ii). Indeed t < p.
      Then d(t,p)<del (by d4).
      Let us show that ft-fp <= 0.
        t \in [x|y].
        d(t,p)<del.
        Then ft <= fp.
        Then ft-fp <= fp-fp.
        fp-fp = 0 (by 1_12_A5).
        Therefore the thesis.
      End.
      Take inv = 1/(t-p). Then inv is a real number.
      inv < 0 (by 5_8_3a). Indeed t-p < 0.
      Then (ft-fp) * inv >= 0 * inv (by 1_18_cc).
      0 * inv = 0 (by 1_16_a).
      Then (ft-fp) * inv >= 0.
      res1(t) = (ft-fp) * inv (by DifferenceQuotient). Indeed res1(t) = DQ(f,p)(t).
      Then res1(t) >= 0.
    End.
    Let us show that if lim(res1,p) exists then lim(res1,p) >= 0.
      res1 is a real map.
      p is a limit point of Dom(res1).
      For every t \in Dom(res1) res1(t) >= 0.
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
    Then res2 is a restriction of DQ(f,p).
    Then p is a limit point of Dom(res2). Indeed Dom(res2) = (p|p+del) and p \in [p|p+del].
    Let us show that if lim(DQ(f,p),p) exists then lim(res2,p) = lim(DQ(f,p),p).
      DQ(f,p) is a real map.
      res2 is a restriction of DQ(f,p).
      p is a limit point of Dom(res2).
      Then the thesis (by LimitOfRestrictedFunction).
    End.
    Therefore lim(res2,p) = d.
    Let us show that for any t \in (p|p+del) res2(t)<=0.
      Assume t \in (p|p+del).
      Take ft = f(t). Then ft is a real number. Indeed t \in Dom(f).
      Then p < t < p+del (by OpenInterval).
      -del < 0.
      Then p-del < p.
      Then p-del < t (by 1_5_ii). Indeed p < t.
      Then d(t,p)<del (by d4).
      Let us show that ft-fp <= 0.
        t \in [x|y].
        d(t,p)<del.
        Then ft <= fp.
        Then ft-fp <= fp-fp.
        fp-fp = 0 (by 1_12_A5).
        Therefore the thesis.
      End.
      Take inv = 1/(t-p). Then inv is a real number.  
      inv > 0 (by 5_8_3b). Indeed t-p > 0.
      Then (ft-fp) * inv <= 0 * inv (by 1_18_bb).
      0 * inv = 0 (by 1_16_a).
      Then (ft-fp) * inv <= 0.
      res2(t) = (ft-fp) * inv (by DifferenceQuotient). Indeed res2(t) = DQ(f,p)(t).
      Then res2(t) <= 0.
    End.
    Let us show that if lim(res2,p) exists then d <= 0.
      res2 is a real map.
      p is a limit point of Dom(res2).
      For every t \in Dom(res2) res2(t) <= 0.
      Therefore the thesis (by 5_8_2a).
    End.
  End.
QED.

Theorem 5_9.
  Let x < y.
  Let f,g be real map such that f,g are defined on [x|y]
  and f is continuous and differentiable on (x|y)
  and g is continuous and differentiable on (x|y).
  Then there exists p \in (x|y) such that
    (f(y)-f(x)) * D(g,p) = (g(y)-g(x)) * D(f,p).
Proof.
  
  # notation to reduce brackets
  Take fx = f(x). Then fx is a real number.
  Take fy = f(y). Then fy is a real number.
  Take gx = g(x). Then gx is a real number.
  Take gy = g(y). Then gy is a real number.
  
  # function h
  Take c = (fy-fx).
  Take d = (gx-gy).
  Then c~g is a real map that is defined on Dom(g) (by ScalingOfRealMap).
  Then d~f is a real map that is defined on Dom(f) (by ScalingOfRealMap).
  Take h = (c~g)++(d~f).
  Then h is a real map that is defined on Dom(c~g) (by AdditionOfRealMaps).
  Indeed Dom(f) = [x|y] = Dom(g).

  # notation to reduce brackets (and ontological checking??)
  Take hx = h(x). Then hx is a real number.
  Take hy = h(y). Then hy is a real number.
  
  # derivative of h
  Let us show that for any t \in (x|y) D(h,t) = (c*D(g,t)) + (d*D(f,t)).
    Suppose t \in (x|y).
    Take a real number A such that D(f,t) = A (by Differentiable).
    Indeed t is an element of Dom(f) that is a limit point of Dom(f) and f is differentiable at t.
    Take a real number B such that D(g,t) = B (by Differentiable).
    Indeed t is an element of Dom(g) that is a limit point of Dom(g) and g is differentiable at t.
    Let us show that D(c~g,t) = c*B.
      t is a limit point of Dom(g).
      g is a real map that is defined on [x|y].
      c is a real number.
      t is an element of (x|y).
      g is differentiable at t. Indeed g is differentiable on (x|y).
      Then the thesis (by DerivativeOfScaledFunction).
    End.
    Let us show that D(d~f,t) = d*A.
      t is a limit point of Dom(f).
      f is a real map that is defined on [x|y].
      d is a real number.
      t is an element of (x|y).
      f is differentiable at t. Indeed f is differentiable on (x|y).
      Then the thesis (by DerivativeOfScaledFunction).
    End.
    Let us show that D(h,t) = (c*B) + (d*A).
      c~g is a real map that is defined on Dom(g) (by ScalingOfRealMap).
      d~f is a real map that is defined on Dom(f) (by ScalingOfRealMap).
      t is an element of (x|y).
      c~g is differentiable at t (by DerivativeOfScaledFunction).
      Indeed t is an element of Dom(g) that is a limit point of Dom(g) and g is differentiable at t.
      d~f is differentiable at t (by DerivativeOfScaledFunction).
      Indeed t is an element of Dom(f) that is a limit point of Dom(f) and f is differentiable at t.
      Then the thesis (by 5_3a).
    End.
  End.

  # h is continuous.
  Let us show that h is continuous.
    Suppose t \in Dom(h).
    c~g, d~f are real map such that Dom(c~g) = Dom(d~f).
    t is an element of Dom(c~g).
    c~g is continuous at t (by ContinuityOfScaledFunction).
    Indeed g is continuous at t and t is a limit point of Dom(g).
    d~f is continuous at t (by ContinuityOfScaledFunction).
    Indeed f is continuous at t and t is a limit point of Dom(f).
    h is continuous at t (by 4_9a). Indeed h = (c~g)++(d~f).
  End.

  # h is differentiable.
  Let us show that h is differentiable on (x|y).
    Suppose t \in (x|y).
    Take a real number A such that D(f,t) = A (by Differentiable).
    Indeed t is an element of Dom(f) that is a limit point of Dom(f) and f is differentiable at t.
    Take a real number B such that D(g,t) = B (by Differentiable).
    Indeed t is an element of Dom(g) that is a limit point of Dom(g) and g is differentiable at t.
    Then D(h,t) is a real number.
    Indeed (c*B) + (d*A) is a real number and D(h,t) = (c*B) + (d*A).
    Then h is differentiable at t (by Differentiable).
    Indeed t is an element of Dom(h) that is a limit point of Dom(h).
  End.

  # it's enough to show D(h,p) = 0.
  Let us show that if there exists p \in (x|y) such that D(h,p) = 0 then the thesis.
    Assume that there exists p \in (x|y) such that D(h,p) = 0.
    Take p \in (x|y) such that D(h,p) = 0.
    Take a real number A such that D(f,p) = A (by Differentiable).
    Indeed p is an element of Dom(f) that is a limit point of Dom(f) and f is differentiable at p.
    Take a real number B such that D(g,p) = B (by Differentiable).
    Indeed p is an element of Dom(g) that is a limit point of Dom(g) and g is differentiable at p.
    Let us show that (fy-fx)*B = (gy-gx)*A.
      D(h,p) = (c*B) + (d*A).
      D(h,p) = 0.
      Then (c*B) + (d*A) = 0.
      Let us show that c*B = -(d*A).
        ((c*B) + (d*A)) - (d*A) = 0 - (d*A).
        0 - (d*A) = -(d*A) + 0 (by 1_12_A2).
        -(d*A) + 0 = -(d*A) (by 1_12_A4).
        ((c*B) + (d*A)) - (d*A) = (c*B) + ((d*A) - (d*A)) (by 1_12_A3).
        (c*B) + ((d*A) - (d*A)) = (c*B) + 0 (by 1_12_A5).
        (c*B) + 0 = c*B (by 1_12_A4).
      End.
      Let us show that -(d*A) = (gy-gx)*A.
        -(d*A) = (-d)*A (by 1_16_c).
        -d = (-gx) + (-(-gy)) (by MinusDist). Indeed gx and -gy are real numbers.
        -(-gy) = gy (by 1_14_d).
        (-gx) + gy = gy + (-gx) (by 1_12_A2).
        Then (-d)*A = (gy-gx)*A.
      End.
      Therefore c*B = (gy-gx)*A.
    End.
  End.

  # h(x) = h(y).
  x \in [x|y] and y \in [x|y].
  Let us show that hx = hy.
    Let us show that hx = (fy*gx)-(gy*fx).
      hx = (c~g)(x) + (d~f)(x) (by Addition).
      (c~g)(x) = c * gx (by Scaling).
      (d~f)(x) = d * fx (by Scaling).
      Then c * gx = ((fy-fx)*gx) = (fy*gx) - (fx*gx).
      Then d * fx = ((gx-gy)*fx) = (gx*fx) - (gy*fx).
      Then h(x) = ((fy*gx)-(fx*gx)) + ((gx*fx)-(gy*fx)).
      ((fy*gx)-(fx*gx)) + ((gx*fx)-(gy*fx)) = (fy*gx) + (-(fx*gx)+((gx*fx)-(gy*fx))) (by 1_12_A3).
      -(fx*gx) + ((gx*fx)-(gy*fx)) = (-(fx*gx)+(gx*fx)) - (gy*fx) (by 1_12_A3).
      -(fx*gx)+(gx*fx) = (gx*fx) - (fx*gx) (by 1_12_A2).
      (gx*fx) - (fx*gx) = 0 (by 1_12_A5). Indeed fx*gx = gx*fx (by 1_12_M2).
      Then (-(fx*gx)+(gx*fx)) - (gy*fx) = 0 - (gy*fx).
      0 - (gy*fx) = -(gy*fx) + 0 (by 1_12_A2).
      -(gy*fx) + 0 = -(gy*fx) (by 1_12_A5).
      Then -(fx*gx) + ((gx*fx)-(gy*fx)) = -(gy*fx).
      Then (fy*gx) + (-(fx*gx)+((gx*fx)-(gy*fx))) = (fy*gx) - (gy*fx).
    End.
    Let us show that hy = -(fx*gy)+(gx*fy).
      hy = (c~g)(y) + (d~f)(y) (by Addition).
      (c~g)(y) = c * gy (by Scaling).
      (d~f)(y) = d * fy (by Scaling).
      Then c * gy = ((fy-fx)*gy) = (fy*gy) - (fx*gy).
      Then d * fy = ((gx-gy)*fy) = (gx*fy) - (gy*fy).
      Then h(y) = ((fy*gy)-(fx*gy)) + ((gx*fy)-(gy*fy)).
      (fy*gy) - (fx*gy) = -(fx*gy) + (fy*gy).
      (gx*fy) - (gy*fy) = -(gy*fy) + (gx*fy).
      Then (-(fx*gy)+(fy*gy)) + (-(gy*fy)+(gx*fy)) = (-(fx*gy) + (fy*gy)) + (-(gy*fy) + (gx*fy)).
      (-(fx*gy)+(fy*gy)) + (-(gy*fy)+(gx*fy))
        = -(fx*gy) + ((fy*gy)+(-(gy*fy)+(gx*fy))) (by 1_12_A3).
      (fy*gy)+(-(gy*fy)+(gx*fy)) = ((fy*gy)-(gy*fy)) + (gx*fy) (by 1_12_A3). 
    End.
    Then hy = -(fx*gy)+(gx*fy).
    -(fx*gy)+(gx*fy) = (gx*fy)-(fx*gy).
    (gx*fy)-(fx*gy) = (fy*gx)-(fx*gy).
    (fy*gx)-(fx*gy) = (fy*gx)-(gy*fx).
  End.

  # ontology check
  h is a real map and (x|y) is a subset of Dom(h). Indeed Dom(h) = [x|y].
  Let us show that for any t \in (x|y) h(t) is a real number.
    Assume t \in (x|y).
    Then h(t) is a real number (by RealMapsEvaluateToRealNumbers).
  End.
    
  # Case 1: h is constant
  Case for any t \in (x|y) h(t) = hx.
    Let us show that for any t \in [x|y] h(t) = hx.
      Assume t \in [x|y].
      Then t = x or t \in (x|y) or t = y.
      Therefore the thesis. Indeed h(x) = hx = h(y).
    End.
    Take p \in (x|y).
    Let us show that D(h,p) = 0.
      h is a real map that is defined on [x|y].
      hx is a real number such that for any t \in [x|y] h(t) = hx.
      p is an element of (x|y).
      Then h is differentiable at p and D(h,p) = 0 (by DerivativeOfConstantFunction).
    End.
    Therefore the thesis. Indeed there exists t \in (x|y) such that D(h,t)=0.
  End.

  # Case 2: h has a maxima in (x|y).
  Case there exists t \in (x|y) such that h(t) > hx.
    Let us show that there exists p \in (x|y) such that p is a local maxima of h.
      h is continuous.
      Dom(h) is nonempty.
      Dom(h) is compact (by Compactness). Indeed Dom(h) = [x|y].
      Then there exists p \in Dom(h) such that
      for any t \in Dom(h) h(t) <= h(p) (by 4_16a).
      Take p \in Dom(h) such that for any t \in Dom(h) h(t) <= h(p).
      Take q \in (x|y) such that h(q) > hx.
      Take hp = h(p). Then hp is a real number.
      Take hq = h(q). Then hq is a real number.
      Let us show that p \in (x|y).
        p \in [x|y].
        hq <= hp. Indeed p,q \in Dom(h).
        Then hx < hp. Indeed hx < hq <= hp.
        Then hp != hx.
        Then p != x.
        hp != hx. Indeed hp != hx = hy.
        Then p != y.
      End.
      Let us show that p is a local maxima of h.
        1 is a positive real number.
        Let us show that for any t \in Dom(h) if d(t,p)<1 then h(t)<=hp.
          Assume t \in Dom(h).
          Then h(t)<=hp.
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
      Take hp = h(p). Then hp is a real number.
      Take hq = h(q). Then hq is a real number.
      Let us show that p \in (x|y).
        p \in [x|y].
        hq >= hp. Indeed p,q \in Dom(h).
        Then hx > hp. Indeed hx > hq >= hp.
        Then hp != hx.
        Then p != x.
        hp != hy. Indeed hp != hx = hy.
        Then p != y.
      End.
      Let us show that p is a local minima of h.
        1 is a positive real number.
        Let us show that for any t \in Dom(h) if d(t,p)<1 then h(t)>=hp.
          Assume t \in Dom(h).
          Then h(t)>=hp.
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

  # 3 cases
  (For any t \in (x|y) h(t) = hx) or (there exists t \in (x|y) such that h(t) > hx)
    or (there exists t \in (x|y) such that h(t) < hx).
QED.

Theorem 5_2.
  Let f be a real map.
  Let p be an element of Dom(f) that is a limit point of Dom(f).
  If f is differentiable at p
  then f is continuous at p.
Proof.
  # notation to reducd brackets and ontological checks
  Take S = (Dom(f))\\{p}. S is a subset of Real and a subset of Dom(f).
  Take fp = f(p). fp is a real number.
  Take g = DQ(f,p). g is a real map that is defined on S.
  # help functions
  Define const1(t) = -p for t in S.
  Then const1 is a constant map with value -p.
  Define const2(t) = fp for t in S.
  Then const2 is a constant map with value fp.
  Define resf(t) = f(t) for t in S.
  Then resf is a restriction of f.
  Define id(t) = t for t in S.
  Then id is the identity map of S and id is a real map.
  Take h1 = id++const1.
  Then h1 is a real map that is defined on S.
  Take h2 = g**(h1).
  Then h2 is a real map that is defined on S.
  Take h3 = h2++const2.
  Then h3 is a real map that is defined on S.
  # f(t) = DQ(f,p)*(t-p) + f(tp)
  Let us show that resf = h3.#! takes long!
    Dom(resf) = S = Dom(h3).
    Let us show that for any t \in S resf(t) = h3(t).
      Assume t \in S.
      Take ft = resf(t). ft is a real number.
      Take h2t = h2(t). h2t is a real number.
      Take h3t = h3(t). h3t is a real number.
      Then h3t = h2(t) + const2(t) (by Addition).
      const2(t) = fp.
      Let us show that h2t = ft - fp.
        h2t = g(t) * h1(t) (by Multiplication). 
        Take inv = 1/(t-p). Indeed t-p != 0.
        g(t) = (ft-fp) * inv (by DifferenceQuotient).
        h1(t) = id(t) + const1(t) (by Addition).
        id(t) = t.
        const1(t) = -p.
        Then h2t = ((ft-fp)*inv)*(t-p).
        ((ft-fp)*inv)*(t-p) = (ft-fp)*(inv*(t-p)).
        inv * (t-p) = (t-p) * inv.
        (t-p) * inv = 1.
        Then h2t = (ft-fp) * 1.
      End.
      Then h3t = (ft-fp) + fp.
      (ft-fp) + fp = ft + (-fp+fp).
      -fp + fp = fp - fp.
      fp - fp = 0.
      Then h3t = ft + 0.
    End.
  End.
  # lim(resf,p) = f(p) by using that f is differentiable at p.
  Assume that f is differentiable at p.
    Let us show that lim(resf,p) = fp.
    lim(id,p) = p (by LimitOfIdentityMap).
    Indeed id is an identity map and p is a limit point of Dom(id).
    lim(const1,p) = -p (by LimitOfConstantFunction).
    Indeed p is a limit point of Dom(const1).
    lim(h1,p) = p - p (by 4_4a).
    Indeed p is a limit point of Dom(id).
    Then lim(h1,p) = 0. Indeed p - p = 0.
    lim(g,p) exists. Indeed f is differentiable at p.
    lim(h2,p) = lim(g,p) * 0 (by 4_4b).
    Indeed p is a limit point of Dom(g).
    Then lim(h2,p) = 0.
    lim(const2,p) = fp (by LimitOfConstantFunction).
    Indeed p is a limit point of Dom(const2).
    lim(h3,p) = 0 + fp (by 4_4a).
    Indeed p is a limit point of Dom(h3).
    Then lim(h3,p) = fp.
    Then lim(resf,p) = fp. Indeed resf = h3.
  End.
  # lim(f,p) = f(p).
  Let us show that lim(f,p) = fp.
    Let us show that for any eps fp is limit of f at p wrt eps.
      Assume that eps is a positive real number.
      Then fp is limit of resf at p wrt eps (by LimitAxiom).
      Indeed p is a limit point of Dom(resf) and lim(resf,p) = fp.
      Let us show that there exists del such that fp is limit of f at p wrt eps and del.
        Take del such that fp is limit of resf at p wrt eps and del (by LimitWrt).
        Indeed p is a limit point of Dom(resf) and fp is limit of resf at p wrt eps.
        Let us show that fp is limit of f at p wrt eps and del.
          For any t \in Dom(resf) if 0<d(t,p)<del then d(f(t),fp)<eps (by LimitWrtAnd).
          Indeed p is a limit point of Dom(resf) and fp is limit of resf at p wrt eps and del.
          Assume t \in Dom(f).
          Take ft = f(t). ft is a real number.
          Let us show that if 0<d(t,p)<del then d(ft,fp)<eps.
            Assume that 0<d(t,p)<del.
            Then t \in S (by SetMinus). #! takes long!
            Indeed t is an element of Dom(f) and t != p.
            Then t \in Dom(resf). Indeed Dom(resf) = S.
            Then d(ft,fp)<eps.
          End.
        End.
      End.
    End.
  End.
  # apply Theorem 4_6.
  Therefore the thesis (by 4_6).
  Indeed p is an element of Dom(f) that is a limit point of Dom(f).
QED.

Theorem 5_10.
  Let x < y.
  Let f be real map that is defined on [x|y].
  Let f be continuous and differentiable on (x|y).
  Then there exists p \in (x|y) such that
    f(y)-f(x) = (y-x) * D(f,p).
Proof.
  # define g to be the identity on [x|y]
  Define g(t) = t for t in [x|y].
  Then g is a real map that is identity map.
  Then g is continuous (by ContinuityOfIdentityMap).
  Let us show that for any t \in (x|y) D(g,t) = 1.
    Assume t \in (x|y).
    t is an element of Dom(g) that is a limit point of Dom(g).
    Then D(g,t) = 1 (by DerivativeOfIdentityMap).
  End.
  Let us show that g is differentiable on (x|y).
    Assume t \in (x|y).
    Then D(g,t) is a real number. Indeed D(g,t) = 1.
    Then g is differentiable at t (by Differentiable).
    Indeed t is an element of Dom(g) that is a limit point of Dom(g).
  End.
  # notation to reduce brackets and ontological checks
  Take fx = f(x). fx is a real number.
  Take fy = f(y). fy is a real number.
  Take gy = g(y). gy is a real number.
  Take gx = g(x). gx is a real number.
  # apply 5_9 to f and g
  Let us show that there exists p \in (x|y) such that (fy-fx)*D(g,p) = (gy-gx)*D(f,p).
    x < y.
    f,g are real map such that f,g are defined on [x|y]
    and f is continuous and differentiable on (x|y)
    and g is continuous and differentiable on (x|y).
    Therefore the thesis (by 5_9).
  End.
  Take p \in (x|y) such that (fy-fx)*D(g,p) = (gy-gx)*D(f,p).
  Then D(g,p) = 1.
  Take a real number A such that D(f,p) = A (by Differentiable).
  Indeed p is an element of Dom(f) that is a limit point of Dom(f) and f is differentiable at p.
  Then (fy-fx)*1 = (y-x)*A. Indeed gy = y and gx = x.
  Then (fy-fx) = (y-x)*A.
  QED.

Theorem 5_11a.
  Let x < y.
  Let f be a real map such that f is defined on (x|y)
  and f is differentiable on (x|y).
  If for any t \in (x|y) D(f,t) >= 0
  then for any s,t \in (x|y) if s <= t then f(s) <= f(t). #! replace by "then f is monotonically increasing."
Proof.
  Assume for any t \in (x|y) D(f,t) >= 0.
  Let us show that for any s,t \in (x|y) if s <= t then f(s) <= f(t).
    Assume that s,t are elements of (x|y) such that s <= t.
    
    # Case 1: s = t.
    Case s = t. Then f(s) = f(t).
    End.

    # Case 2: s < t.
    Case s < t.
      Let us show that [s|t] is a subset of Dom(f).
        Assume that u is an element of [s|t].
        Then s <= u <= t.
      End.
      # restriction of f to [s|t].
      Define resf(u) = f(u) for u in [s|t].
      Then resf is a restriction of f.
      Then resf is a real map.
      Take resfs = resf(s). resfs is a real number.
      Take resft = resf(t). resft is a real number.      
      Let us show that resf is continuous.
        Assume u \in Dom(resf).
        Then u is an element of (x|y).
        Then f is differentiable at u.
        Then f is continuous at u (by 5_2).
        Indeed u is an element of Dom(f) that is a limit point of Dom(f).
        f is continuous at u.
        Then resf is continuous at u (by ContinuityOfRestriction).
      End.
      Let us show that resf is differentiable on (s|t).
        Assume u \in (s|t).
        u is an element of Dom(resf) that is a limit point of Dom(resf).
        f is differentiable at u. Indeed u is an element of (x|y).
        Then resf is differentiable at u (by DerivativeOfRestriction).
      End.
      # apply Theorem 5_10 to restriction of f
      Let us show that there exists p \in (s|t) such that resft - resfs = (t-s) * D(resf,p).
        s < t.
        resf is a real map that is defined on [s|t].
        resf is continuous and differentiable on (s|t).
        Therefore the thesis (by 5_10).
      End.
      # calculating the thesis
      Take p \in (s|t) such that resft - resfs = (t-s) * D(resf,p).
      Take a real number A such that D(resf,p) = A (by Differentiable).
      Indeed p is an element of Dom(resf) that is a limit point of Dom(resf)
        and resf is differentiable at p.
      Then resft - resfs = (t-s) * A.
      Let us show that A >= 0.
        p is an element of Dom(resf) that is a limit point of Dom(resf).
        f is differentiable at p. Indeed p is an element of (x|y).
        Then D(f,p) = D(resf,p) (by DerivativeOfRestriction).
        D(f,p) >= 0. Indeed p is an element of (x|y).
        Therefore the thesis.
      End.
      t - s > 0. Indeed t > s.
      Then (t-s) * A >= 0.
      Then resft - resfs >= 0.
      Then resfs <= resft.
    End.
  End.
QED.

[prove off]
Theorem 5_11b.
  Let x < y.
  Let f be a real map such that f is defined on (x|y)
  and f is differentiable on (x|y).
  If for any t \in (x|y) D(f,t) = 0
  then there exists a real number c such that
    for any t \in (x|y) f(t) = c. #! replace by "then f is constanst."
#! Proof

Theorem 5_11c.
  Let x < y.
  Let f be a real map such that f is defined on (x|y)
  and f is differentiable on (x|y).
  If for any t \in (x|y) D(f,t) <= 0
  then for any s,t \in (x|y) if s <= t then f(s) >= f(t). #! replace by "then f is monotonically decreasing."
#! Proof
[prove on]
