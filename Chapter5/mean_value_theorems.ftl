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


# Lemma

Lemma LimitOfConstantFunction.
  Let c be a real number.
  Let f be a constant map with value c.
  Let p be a limit point of Dom(f).
  Then lim(f,p) = c.
Proof.
  Let us show that for any eps c is limit of f at p wrt eps.
    Assume that eps is a positive real number.
    Take del = 1. del is a positive real number.  
    Let us show that c is limit of f at p wrt eps and del.
      Assume t \in Dom(f) and 0<d(t,p)<del.
      Then d(f(t),c) = 0. Indeed f(t) = c.
      Then d(f(t),c) < eps.
    End.
  End.
QED.

Lemma LimitOfIdentityMap.
  Let f be an identity map.
  Let p be a limit point of Dom(f).
  Then lim(f,p) = p.
Proof.
  p is a real number.
  Let us show that for any eps p is limit of f at p wrt eps.
    Assume that eps is a positive real number.
    Let us show that p is limit of f at p wrt eps and eps.
      Assume t \in Dom(f) and 0<d(t,p)<eps.
      Then d(f(t),p) = d(t,p). Indeed f(t) = t.
      Then d(f(t),p) < eps.
    End.
  End.
QED.

Lemma LimitOfRestrictedFunction.
  Let f be a real map.
  Let g be a restriction of f.
  Let p be a limit point of Dom(g).
  If lim(f,p) exists then lim(g,p) = lim(f,p).
Proof.
  Then p is a limit point of Dom(f) (by LimitPointOfSupset).
  Assume that lim(f,p) exists.
  Take q = lim(f,p). q is a real number.
  Let us show that for any positive real number eps q is limit of g at p wrt eps.
    Assume that eps is a positive real number.
    Take positive real number del such that q is limit of f at p wrt eps and del.
    Indeed q is a real number such that lim(f,p) = q.
    Let us show that q is limit of g at p wrt eps and del.
      Assume t \in Dom(g).
      Then t \in Dom(f). Indeed Dom(g) is a subset of Dom(f).
      Let us show that if 0<d(t,p)<del then d(g(t),q)<eps.
        Assume 0<d(t,p)<del.
        If 0<d(t,p)<del then d(f(t),q)<eps (by LimitWrtAnd).
        Then d(f(t),q)<eps.
        Then d(g(t),q)<eps. Indeed g(t) = f(t).
      End.
    End.
  End.
  Therefore the thesis (by LimitAxiom).
QED.

Lemma LimitOfScaledFunction.
  Let f be a real map.
  Let c be a real number.
  Let p be a limit point of Dom(f).
  If lim(f,p) exists then lim(c~f,p) = c*lim(f,p).
Proof.
  Take S = Dom(f).
  Define g(t) = c for t in S.
  g is a constant map with value c.
  Take h1 = g**f. h1 is a real map that is defined on S.
  Take h2 = c~f. h2 is a real map that is defined on S.
  Let us show that h1 = h2.
    Let us show that Dom(h1) = Dom(h2).
      Dom(h1) = S.
      Dom(h2) = S.
    End.
    Let us show that for any t \in S h1(t) = h2(t).
      Assume t \in S.
      h1(t) = g(t) * f(t).
      g(t) = c.
      Then h1(t) = c*f(t).
      h2(t) = c*f(t).
    End.
  End.
  Assume that lim(f,p) exists.
  Let us show that lim(h1,p) = c*lim(f,p).
    g,f are real map such that Dom(g) = Dom(f).
    p is a limit point of Dom(g).
    If lim(g,p) exists and lim(f,p) exists then lim(h1,p) = lim(g,p)*lim(f,p) (by 4_4b).
    lim(f,p) exists.
    lim(g,p) = c (by LimitOfConstantFunction).
  End.
QED.

# Continuity

Lemma ContinuityOfIdentityMap.
  Let f be a real map that is identity map.
  Then f is continuous.
Proof.
  Assume p \in Dom(f).
  Take fp = f(p). fp is a real number.
  Let us show that f is continuous at p.
    Assume that eps is a positive real number.
    Let us show that f is continuous at p wrt eps.
      Let us show that f is continuous at p wrt eps and eps.
        Assume t \in Dom(f) and 0<d(t,p)<eps.
        Then f(t) = t and fp = p.
        Then d(f(t),f(p)) = d(t,p).
        Then d(f(t),f(p)) < eps.
      End.
    End.
  End.
QED.

Lemma ContinuityOfScaledFunction.
  Let f be a real map.
  Let c be a real number.
  Let p be an element of Dom(f).
  Suppose that f is continuous at p.
  Then c~f is continuous at p.
Proof.
  Take g = c~f. g is a real map.
  p is an element of Dom(g).
  Take fp = f(p). fp is a real number.
  Take gp = g(p). gp is a real number.
  Let us show that g is continuous at p.
    Case c = 0.
      Let us show that for any eps g is continuous at p wrt eps.
        Assume that eps is a positive real number.
        Take del = 1. del is positive real number.
        Let us show that g is continuous at p wrt eps and del.
          Assume t \in Dom(g) and 0<d(t,p)<del.
          Then g(t) = c * f(t) = 0.
          Then gp = c * fp = 0.
          Then d(g(t),gp) = d(0,0) = 0.
          Then d(g(t),gp) < eps.
        End.
      End.
      Then g is continuous at p (by ContinuousAt).
    End.
    Case c > 0.
      Let us show that for any eps g is continuous at p wrt eps.
        Assume that eps is a positive real number.
        Take inv = 1//c. inv is a positive real number.
        inv*eps is a positive real number.
        Then f is continuous at p wrt inv*eps (by ContinuousAt).
        Take del such that f is continuous at p wrt inv*eps and del (by ContinuousAtWrt).
        Indeed f is continuous at p and eps is a positive real number.
        Then for any t \in Dom(f) if 0<d(t,p)<del then d(f(t),fp)<inv*eps (by ContinuousAtWrtAnd).
        Let us show that g is continuous at p wrt eps and del.
          Assume t \in Dom(g) and 0<d(t,p)<del.
          Then t \in Dom(f).
          Take ft = f(t). ft is a real number.
          Take gt = g(t). gt is a real number.
          Then d(ft,fp)<inv*eps.
          Then fp-(inv*eps) < ft < fp+(inv*eps) (by d4).
          Let us show that d(gt,gp)<eps.
            c*(fp-(inv*eps)) < c*ft < c*(fp+(inv*eps)).
            c*(fp-(inv*eps)) = (c*fp) - (c*(inv*eps)).
            c*fp = gp.
            (c*(inv*eps)) = (c*inv)*eps.
            c*inv = 1.
            Then (c*inv)*eps = 1*eps = eps.
            Then c*(fp-(inv*eps)) = gp-eps.
            c*(fp+(inv*eps)) = (c*fp) + (c*(inv*eps)).
            Then (c*fp) + (c*(inv*eps)) = gp+eps.
            Then gp-eps < gt < gp+eps. Indeed gt = c*ft.
          End.
        End.
      End.
      Then g is continuous at p (by ContinuousAt).
    End.
    Case c < 0.
      Take c' = -c. c' is a positive real number.
      Take inv = 1//c'. inv is a positive real number.
      Let us show that for any eps g is continuous at p wrt eps.
        Assume that eps is a positive real number.
        inv*eps is a positive real number.
        Take del such that f is continuous at p wrt inv*eps and del (by ContinuousAtWrtAnd).
        Indeed f is continuous at p.
        Then for any t \in Dom(f) if 0<d(t,p)<del then d(f(t),fp)<inv*eps (by ContinuousAtWrtAnd).
        Let us show that g is continuous at p wrt eps and del.
          Assume t \in Dom(g) and 0<d(t,p)<del.
          Then t \in Dom(f).
          Take ft = f(t). ft is a real number.
          Take gt = g(t). gt is a real number.
          gt = c*ft.
          -gt = -(c*ft).
          -(c*ft) = (-c)*ft.
          Then -gt = c'*ft.
          Then d(ft,fp)<inv*eps.
          Then fp-(inv*eps) < ft < fp+(inv*eps) (by d4).
          Let us show that d(gt,gp)<eps.
              c'*(fp-(inv*eps)) < c'*ft < c'*(fp+(inv*eps)).
              c'*(fp-(inv*eps)) = (c'*fp) - (c'*(inv*eps)).
              c'*fp = (-c)*fp.
              (-c)*fp = -(c*fp).
              c*fp = gp.
              Then c'*fp = -gp.
              (c'*(inv*eps)) = (c'*inv)*eps.
              c'*inv = 1.
              Then (c'*inv)*eps = 1*eps = eps.
              Then c'*(fp-(inv*eps)) = (-gp)-eps.
              c'*(fp+(inv*eps)) = (c'*fp) + (c'*(inv*eps)).
              Then (c'*fp) + (c'*(inv*eps)) = (-gp)+eps.
              Then (-gp)-eps < -gt < (-gp)+eps. Indeed -gt = c'*ft.
              Then gt < gp+eps.
              Then gt > gp-eps.
          End.
        End.
      End.
    End.
  End.
QED.

# Derivative

Lemma DerivativeOfIdentityMap.
  Let f be a real map that is identity map.
  Let p be an element of Dom(f) that is a limit point of Dom(f).
  Then f is differentiable at p and D(f,p) = 1.
Proof.
  Take g = DQ(f,p). g is a real map.
  Let us show that D(f,p) = 1.
    Let us show that lim(g,p) = 1.
      Let us show that for any eps 1 is limit of g at p wrt eps.
        Assume that eps is a positive real number.
        Take del = 1. del is a positive real number.
        Let us show that 1 is limit of g at p wrt eps and del.
          Assume t \in Dom(g) and 0<d(t,p)<del.
          t \in Dom(f).
          Take ft = f(t). ft is a real number.
          Take fp = f(p). fp is a real number.
          Take inv = 1//(t-p). inv is a real number.
          Then g(t) = (ft-fp) // (t-p) (by DifferenceQuotient).
          Indeed p is an element of Dom(f) and g = DQ(f,p).
          (ft-fp) * inv = (t-p) * inv. Indeed ft = t and fp = p.
          (t-p) * inv = 1.
          Then g(t) = 1.
          Then d(g(t),1) = 0.
          Then d(g(t),1)<eps.
        End.
      End.
    End.
  End.
QED.

Lemma DerivativeOfScaledFunction.
  Let f be a real map.
  Let c be a real number.
  Let p be an element of Dom(f) that is a limit point of Dom(f).
  Suppose that f is differentiable at p.
  Then c~f is differentiable at p and D(c~f,p) = c * D(f,p).
Proof.
  Take S = Dom(f).
  Take g = c~f. g is a real map that is defined on S.
  p is an element of Dom(g) that is a limit point of Dom(g).
  Take S' = S \\ {p}.
  Take DQg = DQ(g,p). DQg is a real map that is defined on S'.
  Take DQf = DQ(f,p). DQf is a real map that is defined on S'.
  Take h = c~DQf. h is a real map that is defined on S'.
  Take d = D(f,p). d is a real number.
  Then lim(DQf,p) = d (by DerivativeAxiom).
  Let us show that DQg = h.
    Let us show that Dom(DQg) = Dom(h).
      Dom(DQg) = S'.
      Dom(h) = S'.
    End.
    Let us show that for any t \in S' DQg(t) = h(t).
      Assume t \in S'.
      Take gt = g(t). gt is a real number.
      Take gp = g(p). gp is a real number.
      Take ft = f(t). ft is a real number.
      Take fp = f(p). fp is a real number.
      Take inv = 1/(t-p). inv is a real number.
      DQg(t) = (gt-gp) // (t-p) (by DifferenceQuotient).
      Indeed p is an element of Dom(g).
      gt = c*ft.
      gp = c*fp.
      Then gt-gp = (c*ft)-(c*fp).
      (c*ft)-(c*fp) = c*(ft-fp).
      Then DQg(t) = (c*(ft-fp)) // (t-p).
      Then DQg(t) = (c*(ft-fp))*inv.
      (c*(ft-fp))*inv = c*((ft-fp)*inv).
      Then DQg(t) = c*((ft-fp)*inv).
      DQf(t) = (ft-fp) // (t-p) (by DifferenceQuotient).
      Then DQg(t) = c*DQf(t).
      h(t) = c*DQf(t).
    End.
  End.
  Let us show that lim(h,p) = c*d.
    DQf is a real map.
    c is a real number.
    p is a limit point of Dom(DQf).
    If lim(DQf,p) exists then lim(h,p) = c*lim(DQf,p) (by LimitOfScaledFunction).
    lim(DQf,p) = d.
  End.
  Therefore lim(DQg,p) = c*d. Indeed DQg = h.
  Then D(g,p) = c*d (by DerivativeAxiom).
  Therefore the thesis. Indeed d = D(f,p).
QED.

Lemma DerivativeOfConstantFunction.
  Let c be a real number.
  Let f be a constant map with value c.
  Let p be an element of Dom(f) that is a limit point of Dom(f).
  Then f is differentiable at p and D(f,p) = 0.
Proof.
  Take g = DQ(f,p). g is a real map.
  Let us show that g is a constant map with value 0.
    Assume t \in Dom(g).
    f(t) = c.
    f(p) = c.
    Then g(t) = (c-c) // (t-p).
    c-c = 0.
    Then g(t) = 0 // (t-p).
    0 // (t-p) = 0.
  End.
  Let us show that lim(g,p) = 0.
    0 is a real number.
    g is a constant map with value 0.
    p is a limit point of Dom(g).
    Therefore the thesis (by LimitOfConstantFunction).
  End.
  Then D(f,p) = 0 (by DerivativeAxiom).
QED.

Lemma DerivativeOfRestriction.
  Let f be a real map.
  Let g be a restriction of f.
  Let p be an element of Dom(g) that is a limit point of Dom(g).
  If f is differentiable at p
  then g is differentiable at p and D(g,p) = D(f,p).
Proof.
  p is an element of Dom(f) that is a limit point of Dom(f).
  Assume that f is differentiable at p.
  Take d = D(f,p). d is a real number (by Differentiable).
  Let us show that D(g,p) = d.
    Take hf = DQ(f,p). hf is a real map.
    Take hg = DQ(g,p). hg is a real map.
    Let us show that hg is a restriction of hf.
      Let us show that  Dom(hg) is subset of Dom(hf).
        Dom(hf) = (Dom(f)) \\ {p}.
        Dom(hg) = (Dom(g)) \\ {p}.
        Assume t \in Dom(hg).
        Then t \in Dom(g) and t != p.
        Then t \in Dom(f) and t != p.
        Then t \in Dom(hf).
      End.
      Let us show that for any t \in Dom(hg) hg(t) = hf(t).
        Assume t \in Dom(hg).
        Then t \in Dom(hf) and t \in Dom(g) and t \in Dom(f).
        Take gt = g(t). gt is a real number.
        Take ft = f(t). ft is a real number.
        Take gp = g(p). gp is a real number.
        Take fp = f(p). fp is a real number.
        hg(t) = (gt-gp) // (t-p) (by DifferenceQuotient).
        Indeed hg = DQ(g,p) and p is an element of Dom(g) and g is a real map.
        hf(t) = (ft-fp) // (t-p) (by DifferenceQuotient).
        Then (gt-gp) // (t-p) = (ft-fp) // (t-p). Indeed gt = ft and gp = fp.
        Then hg(t) = hf(t).
      End.
    End.
    Let us show that lim(hg,p) = d.
      hf is a real map.
      hg is a restriction of hf.
      p is a limit point of Dom(hg).
      If lim(hf,p) exists then lim(hg,p) = lim(hf,p) (by LimitOfRestrictedFunction).
      Therefore the thesis. Indeed lim(hf,p) = d.
    End.
  End.
QED.

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
  # Take del near p.
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
  # Take t near p.
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
  # calculating D(f,p) from above:
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
  # notation to reduce brackets and ontological checks
  Take fx = f(x). Then fx is a real number.
  Take fy = f(y). Then fy is a real number.
  Take gx = g(x). Then gx is a real number.
  Take gy = g(y). Then gy is a real number.
  Take c = (fy-fx).
  Take d = (gx-gy).
  Then c~g is a real map that is defined on Dom(g) (by ScalingOfRealMap).
  Then d~f is a real map that is defined on Dom(f) (by ScalingOfRealMap).
  Take h = (c~g)++(d~f).
  Then h is a real map that is defined on Dom(c~g) (by AdditionOfRealMaps).
  Indeed Dom(f) = [x|y] = Dom(g).
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
  # ontological check
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
      hx is a real number.
      h is a constant map with value hx.
      p is an element of Dom(h) that is a limit point of Dom(h).
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
    Case s = t. Then f(s) = f(t). End.
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
