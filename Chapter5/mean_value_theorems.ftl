# MEAN VALUE THEOREMS

[prove off]
[check off]
[read preliminaries.ftl]
[read real-analysis/numbers.ftl]
[read real-analysis/Chapter5/mean_value_theorems_pre.ftl]
[timelimit 20]

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
  Let q be a real number such that lim(f,p)=q.
  Suppose for every t \in Dom(f) f(t)<=0. Then q<=0.
Proof.
  Suppose the contrary.
  Then q is a positive real number.
  Let us show that there exists del such that
  for any t \in Dom(f) if 0<d(t,p)<del then d(f(t),q)<q.
    lim(f,p) = q iff for any eps there exists del such that
      for any t \in Dom(f) if 0<d(t,p)<del then d(f(t),q)<eps (by Limit).
    Indeed f is a real map
      and p is a limit point of Dom(f)
      and q is a real number.
    Therefore the thesis. Indeed lim(f,p) = q and q is a positive real number.
  End.
  Take del such that for any t \in Dom(f)
    if 0<d(t,p)<del then d(f(t),q)<q.
  Take t \in Dom(f) such that 0<d(t,p)<del (by LimitPoint).
  Indeed p is a limit point of Dom(f) and del is a positive real number.
  Take ft = f(t). Then f(t) is a real number.
  Then d(ft,q)<q.
  Then q-q < ft (by d4).
  Then 0 < ft.
  Contradiction.
QED.

Lemma 5_8_2b.
  Let f be a real map.
  Let p be a limit point of Dom(f).
  Let q be a real number such that lim(f,p)=q.
  If for any t \in Dom(f) f(t)>=0 then q>=0.
Proof.
  Assume for any t \in Dom(f) f(t)>=0.
  Suppose the contrary.
  Then -q is a positive real number.
  Let us show that there exists del such that for any t \in Dom(f)
  if 0<d(t,p)<del then d(f(t),q)<-q.
    lim(f,p) = q iff for any eps there exists del such that
    for any t \in Dom(f) if 0<d(t,p)<del then d(f(t),q)<eps (by Limit).
    Therefore the thesis. Indeed lim(f,p) = q and -q is a positive real number.
  End.
  Take del such that for any t \in Dom(f)
    if 0<d(t,p)<del then d(f(t),q)<-q.
  Take t \in Dom(f) such that 0<d(t,p)<del (by LimitPoint).
  Indeed Dom(f) is a subset of Real
    and p is a limit point of Dom(f)
    and del is a positive real number.
  Take ft = f(t). Then ft is a real number.
  Then d(ft,q)<-q.
  Then ft < q+(-q) (by d4).
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
  
  Take real number d such that D(f,p)=d.
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
    Then res1 is a real map that is defined on (p-del|p).
    Indeed for any t \in (p-del|p) DQ(f,p)(t) is a real number.
    Indeed DQ(f,p) is a real map.
    Then p is a limit point of Dom(res1). Indeed Dom(res1) = (p-del|p) and p \in [p-del|p].
    Let us show that if for any t \in Dom(res1) res1(t) = DQ(f,p)(t) then lim(res1,p)=d.
      DQ(f,p), res1 are real map such that Dom(res1) is a subset of Dom(DQ(f,p)).
      p is a limit point of Dom(res1).
      d is a real number such that lim(DQ(f,p),p)=d.
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
    Indeed DQ(f,p) is a real map.
    Then p is a limit point of Dom(res2). Indeed Dom(res2) = (p|p+del) and p \in [p|p+del].
    Let us show that if for any t \in Dom(res2) res2(t) = DQ(f,p)(t) then lim(res2,p)=d.
      DQ(f,p), res2 are real map such that Dom(res2) is a subset of Dom(DQ(f,p)).
      p is a limit point of Dom(res2).  
      lim(DQ(f,p),p)=d.
      Then the thesis (by LimitOfRestrictedFunction).
    End.
    Therefore lim(res2,p)=d. Indeed for any t \in Dom(res2) res2(t) = DQ(f,p)(t).
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
    Let us show that if for any t \in Dom(res2) res2(t)>=0 then d>=0.
      res2 is a real map.
      p is a limit point of Dom(res2).
      d is a real number such that lim(res2,p)=d. 
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
  
  Take real number d such that D(f,p)=d.
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
    Then res1 is a real map.
    Indeed for any t \in (p-del|p) DQ(f,p)(t) is a real number.
    Indeed DQ(f,p) is a real map.
    Then p is a limit point of Dom(res1). Indeed Dom(res1) = (p-del|p) and p \in [p-del|p].
    Let us show that if for any t \in Dom(res1) res1(t) = DQ(f,p)(t) then lim(res1,p)=d.
      DQ(f,p), res1 are real map such that Dom(res1) is a subset of Dom(DQ(f,p)).
      p is a limit point of Dom(res1).
      d is a real number such that lim(DQ(f,p),p)=d.
      Then the thesis (by LimitOfRestrictedFunction).
    End.
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
    Let us show that if for any t \in Dom(res2) res2(t) = DQ(f,p)(t) then  lim(res2,p)=d.
      DQ(f,p), res2 are real map such that Dom(res2) is a subset of Dom(DQ(f,p)).
      p is a limit point of Dom(res2).
      d is a real number such that lim(DQ(f,p),p)=d.
      Then the thesis (by LimitOfRestrictedFunction).
    End.
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
    Let us show that if for any t \in Dom(res2) res2(t)<=0 then d<=0.
      res2 is a real map.
      p is a limit point of Dom(res2).
      d is a real number such that lim(res2,p)=d.
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
  if D(f,p) = A and D(g,p) = B
  then (f(y)-f(x))*B = (g(y)-g(x))*A.
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
  Let us show that for any t \in (x|y) and any real numbers a,b
  if D(f,t) = a and D(g,t) = b then D(h,t) = (c*b) + (d*a).
    Suppose t \in (x|y) and a,b are real numbers such that D(f,t) = a and D(g,t) = b.
    Let us show that D(c~g,t) = c*b.
      t is a limit point of Dom(g).
      g is a real map that is defined on [x|y].
      c is a real number.
      t is an element of (x|y).
      g is differentiable at t. Indeed g is differentiable on (x|y).
      Then the thesis (by DerivativeOfScaledFunction).
    End.
    Let us show that D(d~f,t) = d*a.
      t is a limit point of Dom(f).
      f is a real map that is defined on [x|y].
      d is a real number.
      t is an element of (x|y).
      f is differentiable at t. Indeed f is differentiable on (x|y).
      Then the thesis (by DerivativeOfScaledFunction).
    End.
    Let us show that D(h,t) = (c*b) + (d*a).
      c~g is a real map that is defined on Dom(g) (by ScalingOfRealMap).
      d~f is a real map that is defined on Dom(f) (by ScalingOfRealMap).
      t is an element of (x|y).
      c~g is differentiable at t. Indeed D(c~g,t) = c*b (by DerivativeOfScaledFunction).
      d~f is differentiable at t. Indeed D(d~f,t) = d*a (by DerivativeOfScaledFunction).
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
    Take a real number a such that D(f,t) = a (by Differentiable).
    Indeed t is a limit point of Dom(f) and f is differentiable at t.
    Take a real number b such that D(g,t) = b (by Differentiable).
    Indeed t is a limit point of Dom(g) and g is differentiable at t.
    Then D(h,t) = (c*b) + (d*a).
    Then there exists a real number e such that D(h,t) = e.
    Indeed (c*b) + (d*a) is a real number and D(h,t) = (c*b) + (d*a).
    Then h is differentiable at t. Indeed t is a limit point of Dom(h).
  End.

  # it's enough to show D(h,p) = 0.
  Let us show that if there exists p \in (x|y) such that D(h,p) = 0 then the thesis.
    Assume that there exists p \in (x|y) such that D(h,p) = 0.
    Take p \in (x|y) such that D(h,p) = 0.
    Let us show that if D(f,p) = A and D(g,p) = B then (fy-fx)*B = (gy-gx)*A.
      Assume D(f,p) = A and D(g,p) = B.
      Then D(h,p) = (c*B) + (d*A).
      Let us show that (c*B) + (d*A) = 0.
        h is a real map.
        p is an element of Dom(h) that is a limit point of Dom(h).
        (c*B) + (d*A), 0 are real numbers.
        D(h,p) = (c*B) + (d*A) and D(h,p) = 0.
        Therefore the thesis (by UniquenessOfDerivative).
      End.
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


Theorem 5_10.
  Let x < y.
  Let f be real map that is defined on [x|y].
  Let f be continuous and differentiable on (x|y).
  Then there exists p \in (x|y) such that
  if D(f,p) = A then
    f(y)-f(x) = (y-x) * A.
Proof.
  Define g(t) = t for t in [x|y].
  Then g is a real map that is defined on [x|y].

  [prove off]
  Let us show that g is continuous.
    
  End.

  Let us show that g is differentiable on (x|y).

  End.
  [prove on]

  Take fx = f(x). fx is a real number.
  Take fy = f(y). fy is a real number.
  Take gy = g(y). gy is a real number.
  Take gx = g(x). gx is a real number.
  Take B = 1. B is a real number.

  Let us show that there exists p \in (x|y) such that
  if D(f,p) = A and D(g,p) = B
  then (fy-fx)*B = (gy-gx)*A.
    x < y.
    f,g are real map such that f,g are defined on [x|y]
    and f is continuous and differentiable on (x|y)
    and g is continuous and differentiable on (x|y).
    Therefore the thesis (by 5_9).
  End.
  
  
QED.