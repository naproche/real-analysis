[prove off]
[check off]
[read preliminaries.ftl]
[read real-analysis/numbers.ftl]
[read real-analysis/Chapter5/differentiation_pre.ftl]

Let x,y,z denote real numbers.
Let eps, del denote positive real numbers.
Let o denote an object.
Let f denote a map.

# SETS

Definition ProperSubset.
  A proper subset of S is a set S' such that
    S' is subset of S and
    there exists o \in S such that
      o does not belong to S'.

Definition SetMinus.
  Let S be a set.
  S \\ {o} = {x | x \in S and x != o}.

Definition SetUnion.
  Let S,T be sets.
  S \union T = {x | x \in S or x \in T}.


# INTERVALS

Definition OpenInterval.
  (x | y) is a subset of Real such that
  for every real number i
  i belongs to (x | y) iff x < i < y.

Let S is open interval stand for S = (x | y)
  for some real numbers x,y such that x < y.

Lemma.
  Let S be open interval.
  S is subset of Real.

Definition ClosedInterval.
  [x | y] is a subset of Real such that
  for every real number i
  i belongs to [x | y] iff x <= i <= y.

Let S is closed interval stand for S = [x|y]
  for some nonequal real numbers x,y such that x < y.

#Lemma.
#  Let S be closed interval. 
#  S is nonempty subset of Real and
#  S is bounded above and
#  S is bounded below.


# DIFFERENCE QUOTIENT

Signature. DQ(f,z) is a map.
Axiom DifferenceQuotient.
  Let f be a real map such that f is defined on [x|y].
  Let z be an element of (x|y).
  DQ(f,z) is a real map g such that
    Dom(g) = [x|y] \\ {z} and
    for every t \in Dom(g) g(t) = (f(t) - f(z))*(1/(t-z)).

Lemma.
  Let f be a real map that is defined on [x | y].
  Then for every z \in (x|y)
  there exists DQ(f,z) and
  DQ(f,z) is a real map.


# DERIVATIVE DEFINITION

Axiom.
  Let z be an element of (x|y).
  Then for every t \in [x|y]
  t is a limit point of [x|y] and
  t is a limit point of [x|y] \\ {z} and
  t is a limit point of (x|y) and
  t is a limit point of (x|y) \\ {z}.
#To show that something is a limit point is really annoying.
#Maybe we can use axioms to avoid this problem for now.

Lemma.
  Let f be a real map such that f is defined on [x|y].
  Let z be an element of (x|y).
  Then z is a limit point of Dom(DQ(f,z)).

Signature. D(f,z) is an object.
Axiom.
  Let f be a real map such that f is defined on [x|y].
  Let z be an element of (x|y).
  Let g be DQ(f,z).
  Let t be a real number.
  D(f,z)=t iff lim(g,z)=t.

Definition Differentiable.
  Let f be a real map such that f is defined on [x|y].
  Let z be an element of (x|y).
  f is differentiable at z in x and y iff
    there exists a real number t such that D(f,z)=t.
# Can we somehow remove "in x and y"?

Axiom ConstantFunction.
  Let c be a real numbers.
  There exists a real map f such that f is defined on [x|y]\\{z}
  and for every t \in [x|y]\\{z} f(t) = c.

Axiom IdFunction.
  There exists a real map id such that id is defined on [x|y]\\{z}
  and for every t \in [x|y]\\{z} id(t) = t.

Axiom ResFunction.
  Let f be a real map and S be a subset of Dom(f).
  There exists a real map g such that g is defined on S
  and for every t \in S g(t) = f(t).

Axiom LimitOfId.
  Let z be an element of (x|y).
  Let id be a real map such that id is defined on [x|y]\\{z}
  and for every t \in [x|y]\\{z} id(t) = t.
  Then lim(id,z) = z.

Axiom LimitOfConst.
  Let c be a real number.
  Let z be an element of (x|y).
  Let const be a real map such that const is defined on [x|y]\\{z}
  and for every t \in [x|y]\\{z} const(t) = c.
  Then lim(const,z)=c.



Theorem.
  Let f be a real map such that f is defined on [x|y].
  Let z be an element of (x|y).
  If f is differentiable at z in x and y
  then f is continuous at z.
Proof.
  # constant function with value -f(z)
  Take a real map const1 such that const1 is defined on [x|y]\\{z}
  and for every t \in [x|y]\\{z} const1(t) = -f(z) (by ConstantFunction).
  # restriction of f
  Take a real map Resf such that Resf is defined on [x|y]\\{z}
  and for every t \in [x|y]\\{z} Resf(t) = f(t) (by ResFunction).
  Indeed [x|y]\\{z} is a subset of [x|y].
  # identity map
  Take a real map id such that id is defined on [x|y]\\{z}
  and for every t \in [x|y]\\{z} id(t) = t.
  # constant function with value -z
  Take a real map const2 such that const2 is defined on [x|y]\\{z}
  and for every t \in [x|y]\\{z} const2(t) = -z (by ConstantFunction).
  # difference quotient
  DQ(f,z) is a real map that is defined on [x|y]\\{z}.
  
  # temp1
  Let h1 be Resf++const1.
  # temp2
  Let h2 be DQ(f,z)**(id++const2).

[prove on]
[check on]

  Let us show that h1 = h2.
    Dom(Resf ++ const1) = [x|y]\\{z} = Dom(DQ(f,z)**(id++const2)).
    Let us show that for every t \in [x|y]\\{z} h1(t) = h2(t).
      Assume t \in [x|y]\\{z}.
      h1(t) = Resf(t) + const1(t) = f(t) - f(z).
      Let us show that h2(t) = f(t) - f(z).
        h2(t) = (DQ(f,z))(t) * (id++const2)(t).
        (id++const2)(t) = t - z.
        DQ(f,z)(t) = (f(t) - f(z))*(1/(t-z)).
        ((f(t) - f(z))*(1/(t-z))) * (t - z) = (f(t) - f(z)) * ((1/(t-z)) * (t-z)) = f(t) - f(z).
      End.
      Then h1(t) = f(t) - f(z) = h2(t).
      Then h1(t) = h2(t).
    End.
  End.

  Assume that f is differentiable at z in x and y.

  Let us show that lim(h1,z)=0.
    lim(id,z)=z (by LimitOfId).
    lim(const2,z)=-z (by LimitOfConst).
    Indeed const2 is a  real map such that const2 is defined on [x|y]\\{z} and
    for every t \in [x|y]\\{z} const2(t)=-z.
    Then lim(id++const2,z)=z+-z (by 4_4).
    Indeed Dom(id) = [x|y]\\{z} = Dom(const2) and z is a limit point of Dom(id)
      and z, -z are real numbers such that lim(id,z)=z and lim(const2,z)=-z.
    Then lim(id++const2,z)=0.
    
    Take real number d such that D(f,z)=d.
    Then lim(DQ(f,z),z)=d.
    lim(h2,z)=d*0 (by 4_4).
    Indeed Dom(DQ(f,z)) = [x|y]\\{z} = Dom(id++const2) and z is a limit point of Dom(DQ(f,z))
      and d, 0 are real numbers such that lim(DQ(f,z),z)=d and lim(id++const2,z)=0.
    Then lim(h2,z)=0.
    Then lim(h1,z)=0. Indeed h1 = h2.
  End.

  Take a real map const3 such that const3 is defined on [x|y]\\{z}
  and for every t \in [x|y]\\{z} const3(t) = f(z) (by ConstantFunction).
  Let us show that Resf = h1++const3.
    Dom(Resf) = [x|y]\\{z} = Dom(h1++const3).
    Let us show that for every t \in [x|y]\\{z} Resf(t) = (h1++const3)(t).
      Assume t \in [x|y]\\{z}.
      Resf(t) = f(t).
      Let us show that (h1++const3)(t) = f(t).
        (h1++const3)(t) = h1(t) + f(z).
        h1(t) = f(t) - f(z).
        Then h1(t) + f(z) = f(t).
      End.
      Then Resf(t) = f(t) = (h1++const3)(t).
    End.
  End.

  Let us show that lim(Resf,z)=f(z).
    lim(h1,z)=0.
    lim(const3,z)=f(z) (by LimitOfConst).
    Indeed const3 is a  real map such that const3 is defined on [x|y]\\{z} and
    for every t \in [x|y]\\{z} const3(t) = f(z).
    Then lim(Resf,z)=0+f(z) (by 4_4).
    Indeed Dom(h1) = [x|y]\\{z} = Dom(const3) and z is a limit point of Dom(h1)
      and 0, f(z) are real numbers such that lim(h1,z)=0 and lim(const3,z)=f(z).
    Then lim(Resf,z)=f(z).
  End.

  z is a limit point of Dom(f).
  Let us show that lim(f,z)=f(z).
    Let us show that for any eps there exists del such that for any t \in Dom(f) if 0<d(t,z)<del then d(f(t),f(z))<eps.
      Assume that eps is a positive real number.
      Take del such that for any t \in Dom(Resf) if 0<d(t,z)<del then d(f(t),f(z))<eps (by 4_1).
        Indeed lim(Resf,z)=f(z) and z is a limit point of Dom(Resf).
      Let us show that for any t \in Dom(f) if 0<d(t,z)<del then d(f(t),f(z))<eps.
        Assume t \in Dom(f) and 0<d(t,z)<del.
        Then t != z. Indeed 0<d(t,z).
        Then t \in Dom(Resf). Indeed Dom(Resf) = [x|y]\\{z} and t \in [x|y].
        Then d(f(t),f(z)) < eps. Indeed t \in Dom(Resf) and 0<d(t,z)<del.
      End.
    End.
    Then lim(f,z)=f(z) (by 4_1).
  End.

  Then f is continuous at z (by 4_6). Indeed z is a limit point of Dom(f) and lim(f,z)=f(z).
QED.