[dump on]
[prove off]
[check off]
[read preliminaries.ftl]
[read real-analysis/Chapter5/numbers_filtered.ftl]
[read real-analysis/Chapter5/differentiation_pre.ftl]
[timelimit 30]

[prove off]
[check off]

Let x,y,z denote real numbers.
Let z denote a real number.
Let eps, del denote positive real numbers.
Let o denote an object.
Let f denote a map.

# SETS

Definition SetMinus.
  Let S be a set.
  S \\ {o} = {x | x \in S and x != o}.

Definition SetUnion.
  Let S,T be sets.
  S \union T = {x | x \in S or x \in T}.


# MAP OPERATION

Definition Scaling.
  Let f be a real map.
  Let c be a real number.
  c~f is a map h such that Dom(h) = Dom(f) and
  for any t \in Dom(h) h(t) = c*f(t).


# INTERVALS

Definition OpenInterval.
  (x|y) is a subset of Real such that
  for every real number i
  i belongs to (x|y) iff x < i < y.

Let S is open interval stand for S = (x|y)
  for some real numbers x,y such that x < y.

Definition ClosedInterval.
  [x|y] is a subset of Real such that
  for every real number i
  i belongs to [x|y] iff x <= i <= y.

Let S is closed interval stand for S = [x|y]
  for some real numbers x,y such that x < y.



# DIFFERENCE QUOTIENT

Signature. DQ(f,z) is a map.
Axiom DifferenceQuotient.
  Let f be a real map such that f is defined on [x|y].
  Let z be an element of (x|y).
  DQ(f,z) is a real map g such that
    Dom(g) = [x|y] \\ {z} and
    for every t \in Dom(g) g(t) = (f(t)-f(z))*(1/(t-z)).

Lemma.
  Let f be a real map that is defined on [x|y].
  Let z be an element of (x|y).
  Then there exists DQ(f,z) and
  DQ(f,z) is a real map.


# DERIVATIVE DEFINITION

Axiom LimitPointAxiom.
  Let z be an element of [x|y].
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
Axiom Derivative.
  Let f be a real map such that f is defined on [x|y].
  Let z be an element of (x|y).
  Let t be a real number.
  D(f,z)=t iff lim(DQ(f,z),z)=t.

Definition DifferentiableAtAPoint.
  Let f be a real map.
  Let z be a limit point of Dom(f).
  f is differentiable at z iff
    there exists a real number t such that D(f,z)=t.

Definition Differentiable.
  Let f be a real map.
  Let S be a subset of Dom(f) such that for any t \in S t is a limit point of Dom(f).
  f is differentiable on S iff
    for any t \in S f is differentiable at t.


# some useful functions

Lemma ConstantFunction.
  Let c be a real numbers. Let S be a subset of Real.
  There exists a real map f such that f is defined on S
  and for every t \in S f(t) = c.
Proof.
  Define f(t) = c for t in S.
  Then f is a real map.
QED.

Lemma IdentityFunction.
  Let c be a real numbers. Let S be a subset of Real.
  There exists a real map f such that f is defined on S
  and for every t \in S f(t) = t.
Proof.
  Define f(t) = t for t in S.
  Then f is a real map.
QED.

Lemma RestrictedFunction.
  Let f be a real map and S be a subset of Dom(f).
  There exists a real map g such that g is defined on S
  and for every t \in S g(t) = f(t).
Proof.
  Define g(t) = f(t) for t in S.
  Then g is a real map.
QED.

Lemma LimitOfIdentity.
  Let z be an element of [x|y].
  Let id be a real map such that id is defined on [x|y]\\{z}
  and for every t \in [x|y]\\{z} id(t) = t.
  Then lim(id,z)=z.
Proof.
  Let us show that for any eps there exists del such that for any t \in Dom(id) if 0<d(t,z)<del then d(id(t),z)<eps.
    Assume that eps is a positive real number.
    Let us show that for any t \in Dom(id) if 0<d(t,z)<eps then d(id(t),z)<eps.
      Assume t \in Dom(id) and 0<d(t,z)<eps.
      Then d(id(t),z)<eps. Indeed id(t) = t.
    End.
  End.
  Then lim(id,z)=z (by 4_1).
QED.

Lemma LimitOfConstantFunction.
  Let c be a real number.
  Let z be an element of [x|y].
  Let const be a real map such that const is defined on [x|y]\\{z}
  and for every t \in [x|y]\\{z} const(t) = c.
  Then lim(const,z)=c.
Proof.
  Let us show that for any eps there exists del such that for any t \in Dom(const) if 0<d(t,z)<del then d(const(t),c)<eps.
    Assume that eps is a positive real number.
    Let us show that for any t \in Dom(const) if 0<d(t,z)<1 then d(const(t),c)<eps.
      Assume t \in Dom(const) and 0<d(t,z)<1.
      Then d(const(t),c)=0. Indeed const(t) = c.
      Then d(const(t),c)<eps.
    End.
  End.
  Therefore the thesis (by 4_4).
End.
[prove on] [check on]
# The below lemma seems to follow directly from the definition
# of lim but Freddy was not able to prove it using his laptop 
# (but it works well on Esteban's Laptop)
# Maybe we have to help Naproche a little bit but Freddy is not
# sure how to do this?
Lemma 5_x.
  Let f be a real map.
  Let p be a real number such that p is a limit point of Dom(f).
  Let q be a real number such that lim(f,p)=q.
  Assume that eps is a positive real number.
  Then there exists positive real number del such that for any t \in Dom(f)
  if 0<d(t,p)<del then d(f(t),q)<eps.
Theorem 5_2.
  Let f be a real map such that f is defined on [x|y].
  Let z be an element of (x|y).
  If f is differentiable at z
  then f is continuous at z.
Proof.
  # constant function with value -f(z)
  Define const1(t) = -f(z) for t in [x|y]\\{z}.
  Then const1 is a real map.
  # restriction of f
  Define Resf(t) = f(t) for t in [x|y]\\{z}.
  Then Resf is a real map.
  # identity map
  Define id(t) = t for t in [x|y]\\{z}.
  Then id is a real map.
  # constant function with value -z
  Define const2(t) = -z for t in [x|y]\\{z}.
  Then const2 is a real map.
  # difference quotient
  DQ(f,z) is a real map that is defined on [x|y]\\{z}.
  
  # temp1
  Let h1 be Resf++const1.
  # temp2
  Let h2 be DQ(f,z)**(id++const2).
  # Show: f(t) - f(z) = DQ(f,z) * (t - z)
  Let us show that h1 = h2.
    [check off] [prove off]
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
    [check on] [prove on]
  End.
  
  Assume that f is differentiable at z.
  #Show: f(t) - f(z) -> 0 for t->z.
  Let us show that lim(h1,z)=0.
    [check off] [prove off]
    lim(id,z)=z (by LimitOfIdentity).
    lim(const2,z)=-z (by LimitOfConstantFunction).
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
    [check on] [prove on]
  End.
  # Show: f(t) = f(t) - f(z) + f(z)
  Define const3(t) = f(z) for t in [x|y]\\{z}.
  Then const3 is a real map.
  Let us show that Resf = h1++const3.
    [check off] [prove off]
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
    [check on] [prove on]
  End.
  Let us show that lim(Resf,z)=f(z).
    lim(h1,z)=0.
    lim(const3,z)=f(z) (by LimitOfConstantFunction).
    Indeed const3 is a  real map such that const3 is defined on [x|y]\\{z} and
    for every t \in [x|y]\\{z} const3(t) = f(z).
    Then lim(Resf,z)=0+f(z) (by 4_4).
    Indeed Dom(h1) = [x|y]\\{z} = Dom(const3) and z is a limit point of Dom(h1)
      and 0, f(z) are real numbers such that lim(h1,z)=0 and lim(const3,z)=f(z).
    Then lim(Resf,z)=f(z).
  End.
  z is a limit point of Dom(f).
  
  Let us show that lim(f,z)=f(z).
    [check off] [prove off]
    Let us show that for any eps there exists del such that for any t \in Dom(f) if 0<d(t,z)<del then d(f(t),f(z))<eps.
      Assume that eps is a positive real number.
      Take del such that for any t \in Dom(Resf) if 0<d(t,z)<del then d(Resf(t),f(z))<eps (by 5_x).
      Indeed Resf is a real map and z is a real number such that z is limit point of Dom(Resf) and f(z) is a real number such that lim(Resf,z)=f(z) and eps is a positive real number.
      Let us show that for any t \in Dom(f) if 0<d(t,z)<del then d(f(t),f(z))<eps.
        Assume t \in Dom(f).
        Let us show that if 0<d(t,z)<del then d(f(t),f(z))<eps.
          Assume 0<d(t,z)<del.
          Then t != z.
          Then t \in Dom(Resf). Indeed Dom(Resf) = [x|y]\\{z}.
          Then d(Resf(t),f(z))<eps. Indeed t \in Dom(Resf) and  0<d(t,z)<del.
          Then d(f(t),f(z))<eps. Indeed Resf(t) = f(t).
        End.
      End.
    End.
    [check on] [prove on]
  End.
  
  Then f is continuous at z (by 4_6). Indeed z is a limit point of Dom(f) and lim(f,z)=f(z).
QED.
#Lemma. Contradiction. #TEST 
Theorem 5_3a.
  Let f be a real map such that f is defined on [x|y].
  Let g be a real map such that g is defined on [x|y].
  Let z be an element of (x|y).
  Assume that f is differentiable at z.
  Assume that g is differentiable at z.
  Then f++g is differentiable at z and
  D(f++g,z)=D(f,z)+D(g,z).
Proof.  
  Let A, B be real numbers.  
  DQ(f,z) is a map into Real. DQ(g,z) is a map into Real.
  Dom(DQ(f,z)) = Dom(DQ(g,z)). #necessary for the ontology of the next line.
  
  If DQ(f++g,z) = DQ(f,z)++DQ(g,z) and lim(DQ(f,z),z) = A and lim(DQ(g,z),z) = B 
  then lim(DQ(f++g,z),z) = A + B.
  
  Let us show that DQ(f++g,z) = DQ(f,z)++DQ(g,z).
    Dom(DQ(f++g,z)) = Dom(DQ(f,z)++DQ(g,z)).
    Proof.
      [check off] [prove off]
      Dom(DQ(f++g,z)) = [x|y] \\ {z}. 
      Indeed f++g is a real map and is defined on [x|y].
      Dom(DQ(f,z)++DQ(g,z)) = [x|y] \\ {z}.
      Proof.
        Dom(DQ(f,z)) = (Dom(f)) \\ {z} and Dom(DQ(g,z)) = (Dom(g)) \\ {z}. 
        Dom(f) = Dom(g) = [x|y].
        Then Dom(DQ(f,z)) = Dom(DQ(g,z)) = [x|y] \\ {z}. 
      end.
      [check on] [prove on]
    end.
    
    Let us show that for every t \in Dom(DQ(f++g,z)) 
    DQ(f++g,z)(t) = (DQ(f,z)++DQ(g,z))(t).
      [check off] [prove off]
      Let t belong to Dom(DQ(f++g,z)). Then t != z. 
      Indeed z does not belong to Dom(DQ(f++g,z)).
      t belongs to Dom(f++g).
      DQ(f++g,z)(t) = ((f++g)(t)-((f++g)(z)))//(t-z). 
      ((f++g)(t)-((f++g)(z)))//(t-z) = ((f(t)+g(t))-(f(z)+g(z)))//(t-z).
      ((f(t)+g(t))-(f(z)+g(z))) = ((f(t)+g(t))+(-f(z)-g(z))).
      ((f(t)+g(t))+(-f(z)-g(z))) = (((f(t)+g(t))-f(z))-g(z)).
      ((f(t)+g(t))-(f(z)+g(z)))//(t-z) = (((f(t)+g(t))-f(z))-g(z))//(t-z).
      (((f(t)+g(t))-f(z))-g(z))//(t-z) = ((f(t)+(g(t)-f(z)))-g(z))//(t-z).
      #Ontology
      f(t) is a real number and f(z) is a real number. Indeed f is a real map and t,z \in Dom(f).
      g(t) is a real number and g(z) is a real number. Indeed g is a real map and t,z \in Dom(g).
      ((f(t)+(g(t)-f(z)))-g(z))//(t-z) = ((f(t)+(-f(z) + g(t)))-g(z))//(t-z).
      ((f(t)+(-f(z) + g(t)))-g(z))//(t-z) = (((f(t)-f(z))+g(t))-g(z))//(t-z).
      (((f(t)-f(z))+g(t))-g(z))//(t-z) = ((f(t)-f(z))+(g(t)-g(z)))//(t-z).
      ((f(t)-f(z))+(g(t)-g(z)))//(t-z) = ((f(t)-f(z))//(t-z)) + ((g(t)-g(z))//(t-z)).
      ((f(t)-f(z))//(t-z)) + ((g(t)-g(z))//(t-z)) = DQ(f,z)(t) + DQ(g,z)(t).
      Proof.
        DQ(f,z)(t) = (f(t)-f(z))//(t-z).
        DQ(g,z)(t) = (g(t)-g(z))//(t-z).
        Indeed g is a real map and is defined on [x|y].
      end.
      [check on] [prove on]
    end.
  end. 
  
  D(f++g,z)=D(f,z)+D(g,z).
  Proof.
    lim(DQ(f,z),z) = D(f,z) and lim(DQ(g,z),z) = D(g,z).
    lim(DQ(f++g,z),z) = D(f,z) + D(g,z).
    Therefore the thesis.
  end.
end.
Theorem 5_3b.
  Let f be a real map such that f is defined on [x|y].
  Let g be a real map such that g is defined on [x|y].
  Let z be an element of (x|y).
  Assume that f is differentiable at z.
  Assume that g is differentiable at z.
  Then f**g is differentiable at z
  and D(f**g,z) = ((D(f,z))*g(z)) + (f(z)*(D(g,z))).
Proof.
 
  g(z) is a real number. [x|y]\\{z} is a subset of Real.
  Take real map constg such that constg is defined on [x|y]\\{z}
  and for every x' \in [x|y]\\{z} constg(x') = g(z) (by ConstantFunction).
  Take real map restf such that restf is defined on [x|y]\\{z}
  and for every x' \in [x|y]\\{z} restf(x') = f(x').
 
  Let us show that DQ(f**g,z) = ((DQ(f,z))**constg) ++ (restf**(DQ(g,z))).
    [check off] [prove off]
    Dom(DQ(f**g,z)) =  Dom(((DQ(f,z))**constg) ++ (restf**(DQ(g,z)))).
    Proof.
      Dom(DQ(f**g,z)) = [x|y] \\ {z}. Indeed Dom(f) = Dom(g).
      Dom(((DQ(f,z))**constg) ++ (restf**(DQ(g,z)))) = [x|y] \\ {z}.
      Proof.
        Dom((DQ(f,z))**constg) = [x|y] \\ {z}.
        Dom((restf**(DQ(g,z)))) = [x|y] \\ {z}.
      end.
    end.
    [check on] [prove on]
    Let us show that for every t \in Dom(DQ(f**g,z))
    DQ(f**g,z)(t) = (((DQ(f,z))**constg)++(restf**(DQ(g,z))))(t).
      Let t belong to Dom(DQ(f**g,z)). Then t != z.
      Indeed z does not belong to Dom(DQ(f**g,z)).
      f**g is a real map and t,z \in Dom(f**g).
      (f**g)(t) is a real number and (f**g)(z) is a real number.
      t and z are real numbers such that t != z.
      Then t-z is a real number and t-z != 0.
      DQ(f**g,z)(t) = ((f**g)(t)-(f**g)(z))//(t-z) (by DifferenceQuotient).
      f(t) and g(t) are real numbers and f**g is a real map and t,z \in Dom(f**g).
      [check off] [prove off]
      ((f**g)(t)-(f**g)(z))//(t-z) = (((f(t))*(g(t)))-((f(z))*(g(z))))//(t-z).
      ((f(t)*g(t))-(f(z)*g(z)))//(t-z) = ((((f(t)*g(t))-(f(z)*g(z)))-(f(t)*g(z)))+(f(t)*g(z)))//(t-z).
      Indeed -(f(t)*g(z))+(f(t)*g(z)) = 0.
      ((((f(t)*g(t))-(f(z)*g(z)))-(f(t)*g(z)))+(f(t)*g(z)))//(t-z) = ((((f(t)*g(t))-(f(t)*g(z)))-(f(z)*g(z)))+(f(t)*g(z)))//(t-z).
      ((((f(t)*g(t))-(f(t)*g(z)))-(f(z)*g(z)))+(f(t)*g(z)))//(t-z) = (((f(t)*g(t))-(f(t)*g(z)))+(-(f(z)*g(z))+(f(t)*g(z))))//(t-z).
      ((f(t)*g(t))-(f(t)*g(z))) = ((f(t))*(g(t)-g(z))). (-(f(z)*g(z))+(f(t)*g(z))) = ((g(z))*(f(t)-f(z))).
      (((f(t)*g(t))-(f(t)*g(z)))+(-(f(z)*g(z))+(f(t)*g(z))))//(t-z) = (((f(t))*(g(t)-g(z)))+((g(z))*(f(t)-f(z))))//(t-z).
      (((f(t))*(g(t)-g(z)))+((g(z))*(f(t)-f(z))))//(t-z) = (((f(t))*(g(t)-g(z)))//(t-z)) + (((g(z))*(f(t)-f(z)))//(t-z)).
      [check on] [prove on]
      #Technicalities
      DQ(g,z) is a real map. Dom(DQ(g,z)) = [x|y] \\ {z}. Then t belongs to Dom(DQ(g,z)).
      For every t' \in Dom(DQ(g,z)) DQ(g,z)(t') = (g(t')-g(z))*(1/(t'-z)) (by DifferenceQuotient).
      (g(t)-g(z))//(t-z) = DQ(g,z)(t).

      (f(t)-f(z))//(t-z) = DQ(f,z)(t).
      (((f(t))*(g(t)-g(z)))//(t-z)) + (((g(z))*(f(t)-f(z)))//(t-z)) = (((f(t))*(DQ(g,z)(t)))) + ((g(z))*(DQ(f,z)(t))).
     
      (((DQ(f,z))**constg)++(restf**(DQ(g,z))))(t) = (((f(t))*(DQ(g,z)(t)))) + ((g(z))*(DQ(f,z)(t))).
      Proof.
        [check off] [prove off]
        (((DQ(f,z))**constg)++(restf**(DQ(g,z))))(t) = ((DQ(f,z))**constg)(t) + (restf**(DQ(g,z)))(t).
        ((DQ(f,z))**constg)(t) + (restf**(DQ(g,z)))(t) = ((DQ(f,z)(t))*(constg(t))) + ((restf(t))*(DQ(g,z)(t))).
        constg(t) = g(z) and restf(t) = f(t).
        ((DQ(f,z)(t))*(constg(t))) + ((restf(t))*(DQ(g,z)(t))) = ((DQ(f,z)(t))*(g(z))) + ((f(t))*(DQ(g,z)(t))).
        ((DQ(f,z)(t))*(g(z))) + ((f(t))*(DQ(g,z)(t))) = ((f(t))*(DQ(g,z)(t))) + ((DQ(f,z)(t))*(g(z))).
        ((f(t))*(DQ(g,z)(t))) + ((DQ(f,z)(t))*(g(z))) = ((f(t))*(DQ(g,z)(t))) + ((g(z))*(DQ(f,z)(t))).
        [check on] [prove on]
      end.
    end.
  end. 
 
  D(f**g,z) = ((D(f,z))*g(z)) + (f(z)*(D(g,z))).
  Proof.
    [check off] [prove off]
    lim(DQ(f,z),z) = D(f,z). lim(DQ(g,z),z) = D(g,z).
    lim(constg,z) = g(z).
    lim(restf,z) = f(z).
    Proof. 
      f is continuous at z. Indeed f is differentiable at z.
      Then lim(f,z) = f(z).
      For any eps there exists del such that
      for any t \in Dom(restf) if 0<d(t,z)<del then d(restf(t),f(z))<eps.
    end.

    lim((restf**(DQ(g,z))),z) = f(z) * D(g,z).
    D(f,z) * g(z) is a real number.
    DQ(f,z)**constg is a real map. #Ontology
    lim(DQ(f,z)**constg,z) = D(f,z) * g(z).
    restf is a real map and DQ(g,z) is a real map. #Ontology
    Dom(DQ(g,z)) = Dom(restf). Then restf**DQ(g,z) is a real map. #Ontology
    Dom(DQ(f,z)) = Dom(constg). DQ(f,z)**constg is a real map.  #Ontology
   
    lim((((DQ(f,z))**constg) ++ (restf**(DQ(g,z)))),z) = (D(f,z) * g(z)) + (f(z) * D(g,z)).
    [check on] [prove on]
  end.  
end.

#Lemma. Contradiction. #TEST

Theorem 5_3c.
  Let f be a real map such that f is defined on [x|y].
  Let g be a real map such that g is defined on [x|y].
  Let z be an element of (x|y).
  Assume that f is differentiable at z.
  Assume that g is differentiable at z.
  Assume that for every element e if e belongs to Dom(g) then g(e) != 0.
  Then f|//|g is differentiable at z
  and D(f|//|g,z) = (((g(z))*(D(f,z)))-((D(g,z))*(f(z))))//(g(z)*g(z)).
Proof.
  Take real map constg such that constg is defined on [x|y] \\ {z} and 
  for every x' \in [x|y] \\ {z} constg(x') = g(z).
  Take real map restg such that restg is defined on [x|y] \\ {z} and 
  for every x' \in [x|y] \\ {z} restg(x') = g(x').
  Take real map constf such that constf is defined on [x|y] \\ {z} and 
  for every x' \in [x|y] \\ {z} constf(x') = f(z).
  
  Let us show that 
  DQ(f|//|g,z) = ((constg**DQ(f,z))|--|(DQ(g,z)**constf))|//|(restg**constg).
  
    [check off] [prove off]
    Let us show that Dom(DQ(f|//|g,z)) = Dom(((constg**DQ(f,z))|--|(DQ(g,z)**constf))|//|(restg**constg)).
      Dom(DQ(f|//|g,z)) = [x|y] \\ {z}.
      Dom(((constg**DQ(f,z))|--|(DQ(g,z)**constf))|//|(restg**constg)) = [x|y] \\ {z}.
      Proof.
        Dom(restg**constg) = [x|y] \\ {z}.
          Proof.
            Dom(restg) = [x|y] \\ {z}.
            Dom(constg) = [x|y] \\ {z}.
          end.
        Dom((constg**DQ(f,z))|--|(DQ(g,z)**constf)) = [x|y] \\ {z}.
        Proof.
          Dom(constg**DQ(f,z)) = [x|y] \\ {z}.
          Proof.
            Dom(constg) = [x|y] \\ {z}.
            Dom(DQ(f,z)) = [x|y] \\ {z}.
          end.
          Dom(DQ(g,z)**constf) = [x|y] \\ {z}.
          Proof.
            Dom(DQ(g,z)) = [x|y] \\ {z}.
            Dom(constf) = [x|y] \\ {z}.
          end.
        end.
      end.
    end.
    [check on] [prove on]
    
    Let us show that for every t \in [x|y] \\ {z} 
    DQ(f|//|g,z)(t) = (((constg**DQ(f,z))|--|(DQ(g,z)**constf))|//|(restg**constg))(t).
      Let t belong to [x|y] \\ {z}.
      t \in Dom(DQ(f|//|g,z)).
      DQ(f|//|g,z)(t) = ((f|//|g)(t) - (f|//|g)(z))//(t-z) (by DifferenceQuotient). 
      ((f|//|g)(t) - (f|//|g)(z))//(t-z) = ((f(t)//g(t)) - ((f(z))//(g(z))))//(t-z).
      
      (f(t)//g(t)) - ((f(z))//(g(z))) = ((f(t) * g(z)) // (g(t)*g(z))) - ((f(z)*g(t)) // (g(z)*g(t))). 
      Proof.
        [check off] [prove off]
        f(t)//g(t) = (f(t)//g(t)) * (g(z)//g(z)). 
        Proof.  
          g(z)//g(z) = 1. (f(t)//g(t)) * 1 = f(t)//g(t).
        end.
        (f(t)//g(t)) * (g(z)//g(z)) = (f(t) * g(z)) // (g(t)*g(z)).
        Proof.
          (f(t)//g(t)) * (g(z)//g(z)) = (f(t)*(1/g(t))) * (g(z) * (1/g(z))).
          (f(t)*(1/g(t))) * (g(z) * (1/g(z))) = ((f(t)*(1/g(t))) * g(z)) * (1/g(z)).
          ((f(t)*(1/g(t))) * g(z)) * (1/g(z)) = (f(t) * ((1/g(t)) * g(z))) * (1/g(z)).
          (f(t) * ((1/g(t)) * g(z))) * (1/g(z)) = (f(t) * (g(z) * (1/g(t)))) * (1/g(z)).
          (f(t) * (g(z) * (1/g(t)))) * (1/g(z)) = ((f(t) * g(z)) * (1/g(t))) * (1/g(z)).
          ((f(t) * g(z)) * (1/g(t))) * (1/g(z)) = (f(t)*g(z)) * ((1/g(t))*(1/g(z))).
          (1/g(t))*(1/g(z)) = 1/(g(t)*g(z)).
          Proof.
            ((1/g(t))*(1/g(z)))*(g(t)*g(z)) = ((1/g(t))*g(t))*((1/g(z))*g(z)).
            ((1/g(t))*g(t))*((1/g(z))*g(z)) = 1 * 1 = 1.
          end.
        end.
        f(z)//g(z) = (f(z)*g(t)) // (g(z)*g(t)).
        g(t)*g(z) = g(z)*g(t).  
        [check on] [prove on]
      end.

      ( (f(t)*g(z)) // (g(t)*g(z)) ) - ( (f(z)*g(t)) // (g(z)*g(t)) ) = ( (f(t) * g(z)) - (f(z)*g(t)) ) // (g(z)*g(t)).
      Proof.
        [check off] [prove off]
        ( (f(t)*g(z)) // (g(t)*g(z)) ) - ( (f(z)*g(t)) // (g(z)*g(t)) ) = ((f(t)*g(z))*(1/(g(t)*g(z)))) - ((f(z)*g(t))*(1/(g(z)*g(t)))).
        
        ((f(t)*g(z))*(1/(g(t)*g(z)))) - ((f(z)*g(t))*(1/(g(z)*g(t)))) = ((f(t)*g(z))*(1/(g(z)*g(t)))) - ((f(z)*g(t))*(1/(g(z)*g(t)))).
        ((f(t)*g(z))*(1/(g(z)*g(t)))) - ((f(z)*g(t))*(1/(g(z)*g(t)))) = ((f(t)*g(z)) - (f(z)*g(t))) * (1/(g(z)*g(t))).  
        ((f(t)*g(z)) - (f(z)*g(t))) * (1/(g(z)*g(t))) = ( (f(t) * g(z)) - (f(z)*g(t)) ) // (g(z)*g(t)).
        [check on] [prove on]
      end.
      
      (( (f(t) * g(z)) - (f(z)*g(t)) ) // (g(z)*g(t)))//(t-z) = ( (f(t) * g(z)) - (f(z)*g(t)) ) // ((g(z)*g(t))*(t-z)).
      Proof.
        [check off] [prove off]
        (( (f(t) * g(z)) - (f(z)*g(t)) ) // (g(z)*g(t)))//(t-z) = (( (f(t) * g(z)) - (f(z)*g(t)) )*(1/(g(z)*g(t))))*(1/(t-z)).
        (( (f(t) * g(z)) - (f(z)*g(t)) )*(1/(g(z)*g(t))))*(1/(t-z)) = ( (f(t) * g(z)) - (f(z)*g(t)) ) * ((1/(g(z)*g(t)))*(1/(t-z))).
        (1/(g(z)*g(t)))*(1/(t-z)) = 1/((g(z)*g(t))*(t-z)). #MODULE
        Proof.
          ((1/(g(z)*g(t)))*(1/(t-z)))*((g(z)*g(t))*(t-z)) = (((1/(g(z)*g(t)))*(1/(t-z)))*(g(z)*g(t)))*(t-z).
          (((1/(g(z)*g(t)))*(1/(t-z)))*(g(z)*g(t)))*(t-z) = ((1/(g(z)*g(t)))*((1/(t-z))*(g(z)*g(t))))*(t-z).
          ((1/(g(z)*g(t)))*((1/(t-z))*(g(z)*g(t))))*(t-z) = ((1/(g(z)*g(t)))*((g(z)*g(t))*(1/(t-z))))*(t-z).
          ((1/(g(z)*g(t)))*((g(z)*g(t))*(1/(t-z))))*(t-z) = (((1/(g(z)*g(t)))*(g(z)*g(t)))*(1/(t-z)))*(t-z).
          (((1/(g(z)*g(t)))*(g(z)*g(t)))*(1/(t-z)))*(t-z) = (1*(1/(t-z)))*(t-z).
          (1*(1/(t-z)))*(t-z) = (1/(t-z))*(t-z) = 1.
        end.
        [check on] [prove on]
      end.

      ( (f(t) * g(z)) - (f(z)*g(t)) ) // ((g(z)*g(t))*(t-z)) = (( (f(t) * g(z)) - (f(z)*g(t)) ) // ((g(z)*g(t))*(t-z))) + (( (f(z)*g(z)) - (f(z)*g(z)) ) // ((g(z)*g(t))*(t-z))).
      Proof.
        [check off] [prove off]
        ( (f(z)*g(z)) - (f(z)*g(z)) ) // ((g(z)*g(t))*(t-z)) = 0.
        Proof.
          (f(z)*g(z)) - (f(z)*g(z)) = 0.
          For every real number x' 0 * x' = 0 (by Null).
          ((g(z)*g(t))*(t-z)) is a real number. Then 1/((g(z)*g(t))*(t-z)) is a real number.
          0 // ((g(z)*g(t))*(t-z)) = 0 * (1/((g(z)*g(t))*(t-z))) = 0 (by Null).
        end.
        [check on] [prove on]
      end.

      (( (f(t) * g(z)) - (f(z)*g(t)) ) // ((g(z)*g(t))*(t-z))) + (( (f(z)*g(z)) - (f(z)*g(z)) ) // ((g(z)*g(t))*(t-z))) = (( (f(t) * g(z)) - (f(z)*g(t)) ) + ( (f(z)*g(z)) - (f(z)*g(z)) )) // ((g(z)*g(t))*(t-z)).   
                                                                         
      (( (f(t) * g(z)) - (f(z)*g(t)) ) + ( (f(z)*g(z)) - (f(z)*g(z)) )) // ((g(z)*g(t))*(t-z)) = ((g(z)*(f(t)-f(z))) - (f(z)*(g(t)-g(z)))) // ((g(z)*g(t))*(t-z)).
      Proof.
        [check off] [prove off]
        ( (f(t) * g(z)) - (f(z)*g(t)) ) + ( (f(z)*g(z)) - (f(z)*g(z)) ) = (g(z)*(f(t)-f(z))) - (f(z)*(g(t)-g(z))).
        Proof.
          ( (f(t) * g(z)) - (f(z)*g(t)) ) + ( (f(z)*g(z)) - (f(z)*g(z)) ) = ( (f(t)*g(z)) - (f(z)*g(z)) ) - ( (f(z)*g(t)) - (f(z)*g(z))).
          Proof.
            ( (f(t) * g(z)) - (f(z)*g(t)) ) + ( (f(z)*g(z)) - (f(z)*g(z)) ) = ( (f(t) * g(z)) - (f(z)*g(t)) ) + (- (f(z)*g(z)) + (f(z)*g(z)) ).
            ( (f(t) * g(z)) - (f(z)*g(t)) ) + (- (f(z)*g(z)) + (f(z)*g(z)) ) = (( (f(t) * g(z)) - (f(z)*g(t)) ) - (f(z)*g(z))) + (f(z)*g(z)). 
            (( (f(t) * g(z)) - (f(z)*g(t)) ) - (f(z)*g(z))) + (f(z)*g(z)) = ( (f(t) * g(z)) + ( -(f(z)*g(t))  - (f(z)*g(z)))) + (f(z)*g(z)).
            ( (f(t) * g(z)) + ( -(f(z)*g(t))  - (f(z)*g(z)))) + (f(z)*g(z)) = ( (f(t) * g(z)) + ( - (f(z)*g(z)) -(f(z)*g(t)))) + (f(z)*g(z)).
            ( (f(t) * g(z)) + ( - (f(z)*g(z)) -(f(z)*g(t)))) + (f(z)*g(z)) =  (( (f(t) * g(z)) - (f(z)*g(z)) ) -(f(z)*g(t))) + (f(z)*g(z)).
            (( (f(t) * g(z)) - (f(z)*g(z)) ) -(f(z)*g(t))) + (f(z)*g(z)) = ( (f(t) * g(z)) - (f(z)*g(z)) ) + ( -(f(z)*g(t)) + (f(z)*g(z))).
            -(f(z)*g(t)) + (f(z)*g(z)) = - ( (f(z)*g(t)) - (f(z)*g(z))).
       
            ( (f(t) * g(z)) - (f(z)*g(z)) ) + ( -(f(z)*g(t)) + (f(z)*g(z))) = ( (f(t) * g(z)) - (f(z)*g(z)) ) - ( (f(z)*g(t)) - (f(z)*g(z))).
          end.

          ( (f(t)*g(z)) - (f(z)*g(z)) ) - ( (f(z)*g(t)) - (f(z)*g(z))) = (g(z)*(f(t)-f(z))) - (f(z)*(g(t)-g(z))).
          Proof.
            (f(t)*g(z)) - (f(z)*g(z)) = g(z)*(f(t)-f(z)).
            (f(z)*g(t)) - (f(z)*g(z)) = f(z)*(g(t)-g(z)).
          end.
        end.
        [check on] [prove on]
      end.      

      DQ(f,z) is a real map g such that Dom(g) = [x|y] \\ {z} and
      for every t' \in Dom(g) g(t') = (f(t')-f(z))*(1/(t'-z)) (by DifferenceQuotient).
      DQ(f,z)(t) is a real number.

      DQ(g,z) is a real map g' such that Dom(g') = [x|y] \\ {z} and
      for every t' \in Dom(g') g'(t') = (g(t')-g(z))*(1/(t'-z)) (by DifferenceQuotient).
      DQ(g,z)(t) is a real number.

      ((g(z)*(f(t)-f(z))) - (f(z)*(g(t)-g(z)))) // ((g(z)*g(t))*(t-z)) = ((g(z)*(DQ(f,z)(t))) - ((DQ(g,z)(t))*f(z))) // (g(z)*g(t)).
      Proof.
        ((g(z)*(f(t)-f(z))) - (f(z)*(g(t)-g(z)))) // ((g(z)*g(t))*(t-z)) = ((g(z)*(f(t)-f(z))) // ((g(z)*g(t))*(t-z))) - ((f(z)*(g(t)-g(z))) // ((g(z)*g(t))*(t-z))).

        (g(z)*(f(t)-f(z))) // ((g(z)*g(t))*(t-z)) = (g(z)*(DQ(f,z)(t))) // (g(z)*g(t)).
        Proof.
          (g(z)*(f(t)-f(z))) // ((g(z)*g(t))*(t-z)) = (g(z)*(f(t)-f(z))) * (1/((g(z)*g(t))*(t-z))).
          (g(z)*(f(t)-f(z))) * (1/((g(z)*g(t))*(t-z))) = (g(z)*(f(t)-f(z))) * ((1/(g(z)*g(t))) * (1/(t-z))).
          Proof.
            (1/(g(z)*g(t)))*(1/(t-z)) = 1/((g(z)*g(t))*(t-z)). #MODULE
            Proof.
              1/((g(z)*g(t))*(t-z)) is a real number such that (1/((g(z)*g(t))*(t-z))) * ((g(z)*g(t))*(t-z)) = 1.
              Let us show that if ((1/(g(z)*g(t)))*(1/(t-z)))*((g(z)*g(t))*(t-z)) = 1 then (1/(g(z)*g(t)))*(1/(t-z)) = 1/((g(z)*g(t))*(t-z)).
                [check off] [prove off]
                Assume ((1/(g(z)*g(t)))*(1/(t-z)))*((g(z)*g(t))*(t-z)) = 1.
                (1/((g(z)*g(t))*(t-z))) * ((g(z)*g(t))*(t-z)) = 1.
                Then ((1/(g(z)*g(t)))*(1/(t-z)))*((g(z)*g(t))*(t-z)) = (1/((g(z)*g(t))*(t-z))) * ((g(z)*g(t))*(t-z)).
                (((1/(g(z)*g(t)))*(1/(t-z)))*((g(z)*g(t))*(t-z))) * (1/((g(z)*g(t))*(t-z))) = ((1/((g(z)*g(t))*(t-z))) * ((g(z)*g(t))*(t-z))) * (1/((g(z)*g(t))*(t-z))).
                
                ((1/(g(z)*g(t)))*(1/(t-z)))* (((g(z)*g(t))*(t-z)) * (1/((g(z)*g(t))*(t-z)))) = (1/((g(z)*g(t))*(t-z))) * ( ((g(z)*g(t))*(t-z)) * (1/((g(z)*g(t))*(t-z)))).
                Proof. 
                  ((1/(g(z)*g(t)))*(1/(t-z)))* (((g(z)*g(t))*(t-z)) * (1/((g(z)*g(t))*(t-z)))) = (((1/(g(z)*g(t)))*(1/(t-z)))*((g(z)*g(t))*(t-z))) * (1/((g(z)*g(t))*(t-z))).
                  (1/((g(z)*g(t))*(t-z))) * ( ((g(z)*g(t))*(t-z)) * (1/((g(z)*g(t))*(t-z)))) = ((1/((g(z)*g(t))*(t-z))) * ((g(z)*g(t))*(t-z))) * (1/((g(z)*g(t))*(t-z))).
                end.
                ((1/(g(z)*g(t)))*(1/(t-z)))* 1 = (1/((g(z)*g(t))*(t-z))) * 1.
                (1/(g(z)*g(t)))*(1/(t-z)) = 1/((g(z)*g(t))*(t-z)).
                Proof.
                  (1/(g(z)*g(t)))*(1/(t-z)) = ((1/(g(z)*g(t)))*(1/(t-z)))* 1.
                  1/((g(z)*g(t))*(t-z)) = (1/((g(z)*g(t))*(t-z))) * 1.
                end.
                [check on] [prove on]
              end.
              Let us show that ((1/(g(z)*g(t)))*(1/(t-z)))*((g(z)*g(t))*(t-z)) = 1.
                [check off] [prove off]
                ((1/(g(z)*g(t)))*(1/(t-z)))*((g(z)*g(t))*(t-z)) = (((1/(g(z)*g(t)))*(1/(t-z)))*(g(z)*g(t)))*(t-z).
                (((1/(g(z)*g(t)))*(1/(t-z)))*(g(z)*g(t)))*(t-z) = ((1/(g(z)*g(t)))*((1/(t-z))*(g(z)*g(t))))*(t-z).
                ((1/(g(z)*g(t)))*((1/(t-z))*(g(z)*g(t))))*(t-z) = ((1/(g(z)*g(t)))*((g(z)*g(t))*(1/(t-z))))*(t-z).
                ((1/(g(z)*g(t)))*((g(z)*g(t))*(1/(t-z))))*(t-z) = (((1/(g(z)*g(t)))*(g(z)*g(t)))*(1/(t-z)))*(t-z).
                (((1/(g(z)*g(t)))*(g(z)*g(t)))*(1/(t-z)))*(t-z) = (1*(1/(t-z)))*(t-z).
                (1*(1/(t-z)))*(t-z) = (1/(t-z))*(t-z) = 1.
                [check on] [prove on]
              end.
            end.
          end.
          (g(z)*(f(t)-f(z))) * ((1/(g(z)*g(t))) * (1/(t-z))) = (g(z)*(f(t)-f(z))) * ((1/(t-z) * (1/(g(z)*g(t))))).
          (g(z)*(f(t)-f(z))) * ((1/(t-z) * (1/(g(z)*g(t))))) =  ((g(z)*(f(t)-f(z))) * (1/(t-z))) * (1/(g(z)*g(t))).
          ((g(z)*(f(t)-f(z))) * (1/(t-z))) * (1/(g(z)*g(t))) = (g(z)*((f(t)-f(z)) * (1/(t-z)))) * (1/(g(z)*g(t))).

          (f(t)-f(z)) * (1/(t-z)) = DQ(f,z)(t).
          Proof.
            [check off] [prove off]
            z is an element of (x|y). t belongs to [x|y] \\ {z}.
            DQ(f,z) is a real map. f is a real map such that f is defined on [x|y].
            DQ(f,z) is a real map g such that Dom(g) = [x|y] \\ {z} and
            for every t' \in Dom(g) g(t') = (f(t')-f(z))*(1/(t'-z)) (by DifferenceQuotient).
            DQ(f,z)(t) = (f(t)-f(z)) * (1/(t-z)).   
            [check on] [prove on]
          end.

          (g(z)*((f(t)-f(z)) * (1/(t-z)))) * (1/(g(z)*g(t))) = (g(z)*(DQ(f,z)(t))) * (1/(g(z)*g(t))).
          (g(z)*(DQ(f,z)(t))) * (1/(g(z)*g(t))) = (g(z)*(DQ(f,z)(t))) // (g(z)*g(t)). 
        end.
        
        (f(z)*(g(t)-g(z))) // ((g(z)*g(t))*(t-z)) = ((DQ(g,z)(t))*f(z)) // (g(z)*g(t)).
        Proof.
          (f(z)*(g(t)-g(z))) // ((g(z)*g(t))*(t-z)) = (f(z)*(g(t)-g(z))) * (1/((g(z)*g(t))*(t-z))).
          (f(z)*(g(t)-g(z))) * (1/((g(z)*g(t))*(t-z))) = (f(z)*(g(t)-g(z))) * ((1/(g(z)*g(t))) * (1/(t-z))).
          Proof.
            (1/(g(z)*g(t)))*(1/(t-z)) = 1/((g(z)*g(t))*(t-z)). #MODULE
            Proof.
              1/((g(z)*g(t))*(t-z)) is a real number such that (1/((g(z)*g(t))*(t-z))) * ((g(z)*g(t))*(t-z)) = 1.
              Let us show that if ((1/(g(z)*g(t)))*(1/(t-z)))*((g(z)*g(t))*(t-z)) = 1 then (1/(g(z)*g(t)))*(1/(t-z)) = 1/((g(z)*g(t))*(t-z)).
                [check off] [prove off]
                Assume ((1/(g(z)*g(t)))*(1/(t-z)))*((g(z)*g(t))*(t-z)) = 1.
                (1/((g(z)*g(t))*(t-z))) * ((g(z)*g(t))*(t-z)) = 1.
                Then ((1/(g(z)*g(t)))*(1/(t-z)))*((g(z)*g(t))*(t-z)) = (1/((g(z)*g(t))*(t-z))) * ((g(z)*g(t))*(t-z)).
                (((1/(g(z)*g(t)))*(1/(t-z)))*((g(z)*g(t))*(t-z))) * (1/((g(z)*g(t))*(t-z))) = ((1/((g(z)*g(t))*(t-z))) * ((g(z)*g(t))*(t-z))) * (1/((g(z)*g(t))*(t-z))).
                
                ((1/(g(z)*g(t)))*(1/(t-z)))* (((g(z)*g(t))*(t-z)) * (1/((g(z)*g(t))*(t-z)))) = (1/((g(z)*g(t))*(t-z))) * ( ((g(z)*g(t))*(t-z)) * (1/((g(z)*g(t))*(t-z)))).
                Proof. 
                  ((1/(g(z)*g(t)))*(1/(t-z)))* (((g(z)*g(t))*(t-z)) * (1/((g(z)*g(t))*(t-z)))) = (((1/(g(z)*g(t)))*(1/(t-z)))*((g(z)*g(t))*(t-z))) * (1/((g(z)*g(t))*(t-z))).
                  (1/((g(z)*g(t))*(t-z))) * ( ((g(z)*g(t))*(t-z)) * (1/((g(z)*g(t))*(t-z)))) = ((1/((g(z)*g(t))*(t-z))) * ((g(z)*g(t))*(t-z))) * (1/((g(z)*g(t))*(t-z))).
                end.
                ((1/(g(z)*g(t)))*(1/(t-z)))* 1 = (1/((g(z)*g(t))*(t-z))) * 1.
                (1/(g(z)*g(t)))*(1/(t-z)) = 1/((g(z)*g(t))*(t-z)).
                Proof.
                  (1/(g(z)*g(t)))*(1/(t-z)) = ((1/(g(z)*g(t)))*(1/(t-z)))* 1.
                  1/((g(z)*g(t))*(t-z)) = (1/((g(z)*g(t))*(t-z))) * 1.
                end.
                [check on] [prove on]
              end.
              Let us show that ((1/(g(z)*g(t)))*(1/(t-z)))*((g(z)*g(t))*(t-z)) = 1.
                [check off] [prove off]
                ((1/(g(z)*g(t)))*(1/(t-z)))*((g(z)*g(t))*(t-z)) = (((1/(g(z)*g(t)))*(1/(t-z)))*(g(z)*g(t)))*(t-z).
                (((1/(g(z)*g(t)))*(1/(t-z)))*(g(z)*g(t)))*(t-z) = ((1/(g(z)*g(t)))*((1/(t-z))*(g(z)*g(t))))*(t-z).
                ((1/(g(z)*g(t)))*((1/(t-z))*(g(z)*g(t))))*(t-z) = ((1/(g(z)*g(t)))*((g(z)*g(t))*(1/(t-z))))*(t-z).
                ((1/(g(z)*g(t)))*((g(z)*g(t))*(1/(t-z))))*(t-z) = (((1/(g(z)*g(t)))*(g(z)*g(t)))*(1/(t-z)))*(t-z).
                (((1/(g(z)*g(t)))*(g(z)*g(t)))*(1/(t-z)))*(t-z) = (1*(1/(t-z)))*(t-z).
                (1*(1/(t-z)))*(t-z) = (1/(t-z))*(t-z) = 1.
                [check on] [prove on]
              end.
            end.
          end.
          
          (f(z)*(g(t)-g(z))) * ((1/(g(z)*g(t))) * (1/(t-z))) = (f(z)*(g(t)-g(z))) * ((1/(t-z) * (1/(g(z)*g(t))))).
          (f(z)*(g(t)-g(z))) * ((1/(t-z) * (1/(g(z)*g(t))))) =  ((f(z)*(g(t)-g(z))) * (1/(t-z))) * (1/(g(z)*g(t))).
          ((f(z)*(g(t)-g(z))) * (1/(t-z))) * (1/(g(z)*g(t))) = (f(z)*((g(t)-g(z)) * (1/(t-z)))) * (1/(g(z)*g(t))).

          (g(t)-g(z)) * (1/(t-z)) = DQ(g,z)(t).
          Proof.
            [check off] [prove off]
            z is an element of (x|y). t belongs to [x|y] \\ {z}.
            DQ(g,z) is a real map. g is a real map such that g is defined on [x|y].
            DQ(g,z) is a real map h such that Dom(h) = [x|y] \\ {z} and
            for every t' \in Dom(h) h(t') = (g(t')-g(z))*(1/(t'-z)) (by DifferenceQuotient).
            DQ(g,z)(t) = (g(t)-g(z)) * (1/(t-z)). 
            [check on] [prove on]
          end.

          (f(z)*((g(t)-g(z)) * (1/(t-z)))) * (1/(g(z)*g(t))) = (f(z)*(DQ(g,z)(t))) * (1/(g(z)*g(t))).
          (f(z)*(DQ(g,z)(t))) * (1/(g(z)*g(t))) = ((DQ(g,z)(t))*f(z)) * (1/(g(z)*g(t))).
          ((DQ(g,z)(t))*f(z)) * (1/(g(z)*g(t))) = ((DQ(g,z)(t))*f(z)) // (g(z)*g(t)). 
        end.
      end.
      
      ((g(z)*(DQ(f,z)(t))) - ((DQ(g,z)(t))*f(z))) // (g(z)*g(t)) = ((g(z)*(DQ(f,z)(t))) - ((DQ(g,z)(t))*f(z))) // ((restg**constg)(t)).
      Proof.
        g(z)*g(t) = (restg**constg)(t).
        Proof.
          [check off] [prove off]
          (restg**constg)(t) = restg(t) * constg(t).
          restg(t) * constg(t) = g(t) * g(z).
          g(t) * g(z) = g(z) * g(t).
          (restg**constg)(t) = (constg**restg)(t).
          [check on] [prove on]
        end.  
      end.

      ((g(z)*(DQ(f,z)(t))) - ((DQ(g,z)(t))*f(z))) // ((restg**constg)(t)) = (((constg**DQ(f,z))(t)) - ((DQ(g,z)(t))*f(z))) // ((restg**constg)(t)).
      Proof. 
        g(z)*(DQ(f,z)(t)) = (constg**DQ(f,z))(t).
        Proof.
          [check off] [prove off]
          (constg**DQ(f,z))(t) = constg(t) * (DQ(f,z)(t)).
          constg(t) * (DQ(f,z)(t)) = g(z) * (DQ(f,z)(t)).
          [check on] [prove on]
        end.
      end.

      [check off] [prove off]
      (((constg**DQ(f,z))(t)) - ((DQ(g,z)(t))*f(z))) // ((restg**constg)(t)) = (((constg**DQ(f,z))(t)) - ((DQ(g,z)**constf)(t))) // ((restg**constg)(t)).
      Proof.
        (DQ(g,z)**constf)(t) = (DQ(g,z)(t)) * constf(t).
        (DQ(g,z)(t)) * constf(t) = (DQ(g,z)(t)) * f(z).
      end.

      (((constg**DQ(f,z))(t)) - ((DQ(g,z)**constf)(t))) // ((restg**constg)(t)) = (((constg**DQ(f,z))|--|(DQ(g,z)**constf))(t)) // ((restg**constg)(t)).
      Proof.
        ((constg**DQ(f,z))|--|(DQ(g,z)**constf))(t) = ((constg**DQ(f,z))(t)) - ((DQ(g,z)**constf)(t)).
      end.
      [check on] [prove on]

      (((constg**DQ(f,z))|--|(DQ(g,z)**constf))(t)) // ((restg**constg)(t)) = (((constg**DQ(f,z))|--|(DQ(g,z)**constf))|//|(restg**constg))(t).
    end.
  end.

  Let us show that D(f|//|g,z) = (((g(z))*(D(f,z)))-((D(g,z))*(f(z))))//(g(z)*g(z)).
  Proof.
    lim(DQ(f|//|g,z),z) = D(f|//|g,z).

    lim(((constg**DQ(f,z))|--|(DQ(g,z)**constf))|//|(restg**constg),z) = D(f|//|g,z).
    Proof.
      DQ(f|//|g,z) = ((constg**DQ(f,z))|--|(DQ(g,z)**constf))|//|(restg**constg). #PROBLEM
    end.
    
    lim(constg**DQ(f,z),z) = g(z) * D(f,z).
    Proof.
      lim(constg,z) = g(z). #PROBLEM
      lim(DQ(f,z),z) = D(f,z).
    end.

    lim(DQ(g,z)**constf,z) = D(g,z) * f(z).
    Proof.
      lim(DQ(g,z),z) = D(g,z) * f(z).
      lim(constf,z) = f(z). #PROBLEM
    end.      
    
    lim(restg**constg,z) = g(z)*g(z).
    Proof.
      lim(restg,z) = g(z). #PROBLEM
      lim(constg,z) = g(z). #PROBLEM
    end.

    lim((constg**DQ(f,z))|--|(DQ(g,z)**constf),z) = (g(z) * D(f,z)) - (D(g,z) * f(z)). #PROBLEM

    lim(((constg**DQ(f,z))|--|(DQ(g,z)**constf))|//|(restg**constg),z) = ((g(z) * D(f,z)) - (D(g,z) * f(z))) // (g(z)*g(z)). #PROBLEM
    
  end.

end.

Lemma. Contradiction. #TEST