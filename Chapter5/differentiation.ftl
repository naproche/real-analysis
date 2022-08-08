[prove off]
[check off]
[read preliminaries.ftl]
[read real-analysis/numbers.ftl]
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
  Assume that f is differentiable at z.
  #Show: f(t) - f(z) -> 0 for t->z.
  Let us show that lim(h1,z)=0.
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
  End.
  # Show: f(t) = f(t) - f(z) + f(z)
  Define const3(t) = f(z) for t in [x|y]\\{z}.
  Then const3 is a real map.
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
      Dom(DQ(f++g,z)) = [x|y] \\ {z}. 
      Indeed f++g is a real map and is defined on [x|y].
      Dom(DQ(f,z)++DQ(g,z)) = [x|y] \\ {z}.
      Proof.
        Dom(DQ(f,z)) = (Dom(f)) \\ {z} and Dom(DQ(g,z)) = (Dom(g)) \\ {z}. 
        Dom(f) = Dom(g) = [x|y].
        Then Dom(DQ(f,z)) = Dom(DQ(g,z)) = [x|y] \\ {z}. 
      end.
    end.
    Let us show that for every t \in Dom(DQ(f++g,z)) 
    DQ(f++g,z)(t) = (DQ(f,z)++DQ(g,z))(t).
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
    Dom(DQ(f**g,z)) =  Dom(((DQ(f,z))**constg) ++ (restf**(DQ(g,z)))).
    Proof.
      Dom(DQ(f**g,z)) = [x|y] \\ {z}. Indeed Dom(f) = Dom(g).
      Dom(((DQ(f,z))**constg) ++ (restf**(DQ(g,z)))) = [x|y] \\ {z}.
      Proof.
        Dom((DQ(f,z))**constg) = [x|y] \\ {z}.
        Dom((restf**(DQ(g,z)))) = [x|y] \\ {z}.
      end.
    end.
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
      ((f**g)(t)-(f**g)(z))//(t-z) = (((f(t))*(g(t)))-((f(z))*(g(z))))//(t-z).
      ((f(t)*g(t))-(f(z)*g(z)))//(t-z) = ((((f(t)*g(t))-(f(z)*g(z)))-(f(t)*g(z)))+(f(t)*g(z)))//(t-z).
      Indeed -(f(t)*g(z))+(f(t)*g(z)) = 0.
      ((((f(t)*g(t))-(f(z)*g(z)))-(f(t)*g(z)))+(f(t)*g(z)))//(t-z) = ((((f(t)*g(t))-(f(t)*g(z)))-(f(z)*g(z)))+(f(t)*g(z)))//(t-z).
      ((((f(t)*g(t))-(f(t)*g(z)))-(f(z)*g(z)))+(f(t)*g(z)))//(t-z) = (((f(t)*g(t))-(f(t)*g(z)))+(-(f(z)*g(z))+(f(t)*g(z))))//(t-z).
      ((f(t)*g(t))-(f(t)*g(z))) = ((f(t))*(g(t)-g(z))). (-(f(z)*g(z))+(f(t)*g(z))) = ((g(z))*(f(t)-f(z))).
      (((f(t)*g(t))-(f(t)*g(z)))+(-(f(z)*g(z))+(f(t)*g(z))))//(t-z) = (((f(t))*(g(t)-g(z)))+((g(z))*(f(t)-f(z))))//(t-z).
      (((f(t))*(g(t)-g(z)))+((g(z))*(f(t)-f(z))))//(t-z) = (((f(t))*(g(t)-g(z)))//(t-z)) + (((g(z))*(f(t)-f(z)))//(t-z)).
      #Technicalities
      DQ(g,z) is a real map. Dom(DQ(g,z)) = [x|y] \\ {z}. Then t belongs to Dom(DQ(g,z)).
      For every t' \in Dom(DQ(g,z)) DQ(g,z)(t') = (g(t')-g(z))*(1/(t'-z)) (by DifferenceQuotient).
      (g(t)-g(z))//(t-z) = DQ(g,z)(t).

      (f(t)-f(z))//(t-z) = DQ(f,z)(t).
      (((f(t))*(g(t)-g(z)))//(t-z)) + (((g(z))*(f(t)-f(z)))//(t-z)) = (((f(t))*(DQ(g,z)(t)))) + ((g(z))*(DQ(f,z)(t))).
     
      (((DQ(f,z))**constg)++(restf**(DQ(g,z))))(t) = (((f(t))*(DQ(g,z)(t)))) + ((g(z))*(DQ(f,z)(t))).
      Proof.
        (((DQ(f,z))**constg)++(restf**(DQ(g,z))))(t) = ((DQ(f,z))**constg)(t) + (restf**(DQ(g,z)))(t).
        ((DQ(f,z))**constg)(t) + (restf**(DQ(g,z)))(t) = ((DQ(f,z)(t))*(constg(t))) + ((restf(t))*(DQ(g,z)(t))).
        constg(t) = g(z) and restf(t) = f(t).
        ((DQ(f,z)(t))*(constg(t))) + ((restf(t))*(DQ(g,z)(t))) = ((DQ(f,z)(t))*(g(z))) + ((f(t))*(DQ(g,z)(t))).
        ((DQ(f,z)(t))*(g(z))) + ((f(t))*(DQ(g,z)(t))) = ((f(t))*(DQ(g,z)(t))) + ((DQ(f,z)(t))*(g(z))).
        ((f(t))*(DQ(g,z)(t))) + ((DQ(f,z)(t))*(g(z))) = ((f(t))*(DQ(g,z)(t))) + ((g(z))*(DQ(f,z)(t))).
      end.
    end.
  end.
 
  D(f**g,z) = ((D(f,z))*g(z)) + (f(z)*(D(g,z))).
  Proof.
   
    lim(DQ(f,z),z) = D(f,z). lim(DQ(g,z),z) = D(g,z).
    lim(constg,z) = g(z).
    lim(restf,z) = f(z).
    Proof. #Interesting... the following suffices.
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
  end.  
end.



Theorem 5_3c.
  Let f be a real map such that f is defined on [x|y].
  Let g be a real map such that g is defined on [x|y].
  Let z be an element of (x|y).
  Assume that f is differentiable at z.
  Assume that g is differentiable at z.
  Assume that for every element e if e belongs to Dom(g) then g(e) != 0.
  Then f|//|g is differentiable at z
  and D(f|//|g,z) = (((g(z))*(D(f,z)))-((D(g,z))*(f(z))))//(g(x)*g(x)).






# Mean Value Theorems

Definition 5_7a.
  Let f be a real map.
  Let p be an element of Dom(f).
  f has local minima at p iff there exists del such that
    for any t \in Dom(f) if d(t,p)<del then f(t)>=f(p).

Definition 5_7b.
  Let f be a real map.
  Let p be an element of Dom(f).
  f has local maxima at p iff there exists del such that
    for any t \in Dom(f) if d(t,p)<del then f(t)<=f(p).

Lemma 5_8_1.
  Let S be a subset of Real.
  Let p be a real number.
  If p is a limit point of S then for any eps there exists t \in S such that 0<d(t,p)<eps.
Proof.
  Assume that p is a limit point of S.
  Take sequence f such that f is into S and f unequally converges to p (by LimitPoint).
  Let eps be a positive real number.
  Take a positive integer N such that for any positive integer n
    if N<n then 0<d(f(n),p)<eps (by UneqConv).
QED.

Lemma 5_8_2a.
  Let f be a real map.
  Let p be a real number such that p is a limit point of Dom(f).
  Let q be a real number such that lim(f,p)=q.
  Suppose for every t \in Dom(f) f(t)<=0. Then q<=0.
Proof.
  Suppose the contrary.
  Then q is a positive real number.
  Take del such that for any t \in Dom(f)
    if 0<d(t,p)<del then d(f(t),q)<q (by 5_x).
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
  Take del such that for any t \in Dom(f)
    if 0<d(t,p)<del then d(f(t),q)<-q (by 5_x).
  Take t \in Dom(f) such that 0<d(t,p)<del (by 5_8_1).
  Indeed Dom(f) is a subset of Real and p is a limit point of Dom(f) and del is a positive real number.
  Then d(f(t),q)<-q.
  Then f(t) < q+(-q) (by d4).
  Then f(t) < 0.
  Contradiction.
QED.

Lemma LimitOfRestrictedFunction.
  Let f,g be real map such that Dom(g) is a subset of Dom(f).
  Let p be a limit point of Dom(g).
  Let q be a real number.
  If for any t \in Dom(g) g(t) = f(t) and lim(f,p)=q then lim(g,p)=q.
Proof.
  Assume for any t \in Dom(g) g(t) = f(t) and lim(f,p)=q.
  Let us show that lim(g,p)=q.
    Assume that eps is a positive real number.
    Take del such that for any t \in Dom(f) if 0<d(t,p)<del then d(f(t),q)<eps (by 5_x).
    Let us show that for any t \in Dom(g) if 0<d(t,p)<del then d(g(t),q)<eps.
      Take t \in Dom(g).  
      Then t \in Dom(f). Indeed Dom(g) is a subset of Dom(f).
      Let us show that if 0<d(t,p)<del then d(g(t),q)<eps.
        Assume 0<d(t,p)<del.
        Then d(f(t),q)<eps.
        THen d(g(t),q)<eps. Indeed g(t) = f(t).
      End.
    End.
  End.
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
  If f is differentiable at p and f has local minima at p
  then D(f,p)=0.
Proof.
  Assume f is differentiable at p and f has local minima at p.
  Let us show that there exists del such that x<p-del and p+del<y
      and for any t \in [x|y] if d(t,p)<del then f(t)>=f(p).
    Take positive real number del' such that for any t \in [x|y] if d(t,p)<del' then f(t)>=f(p) (by 5_7a).
    Indeed f has local minima at p.
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


  Let us show that d<=0.
    Let us show that (p-del|p) is a subset of Dom(DQ(f,p)).
      Assume t \in (p-del|p).
      Then p-del < t < p (by OpenInterval).
      Then x < t and t < y and t != p. Indeed x < p-del and p < y.
      Then t \in Dom(DQ(f,p)). Indeed Dom(DQ(f,p)) = [x|y]\\{p}.
    End.
    Take a real map res1 such that res1 is defined on (p-del|p) and
      for every t \in (p-del|p) res1(t) = DQ(f,p)(t) (by RestrictedFunction).
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
      Then (f(t)-f(p))*(1/(t-p)) <= 0*0 = 0.
      res1(t) = (f(t)-f(p))*(1/(t-p)) (by DifferenceQuotient). Indeed res1(t) = DQ(f,p)(t).
      Then res1(t) <= 0.
    End.
    Let us show that if for every t \in Dom(res1) res1(t)<=0 then d<=0.
      res1 is a real map.
      p is a real number such that p is a limit point of Dom(res1).
      d is a real number such that lim(res1,p)=d.
      Therefore the thesis (by 5_8_2a).
    End.
  End.
  Let us show that d>=0.
    Let us show that (p|p+del) is a subset of Dom(DQ(f,p)).
      Assume t \in (p|p+del).
      Then p < t < p+del (by OpenInterval).
      Then x < t and t < y and t != p. Indeed x < p and p+del < y.
      Then t \in Dom(DQ(f,p)). Indeed Dom(DQ(f,p)) = [x|y]\\{p}.
    End.
    Take a real map res2 such that res2 is defined on (p|p+del) and
      for every t \in (p|p+del) res2(t) = DQ(f,p)(t) (by RestrictedFunction).
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
      Then (f(t)-f(p))*(1/(t-p)) >= 0*0 = 0.
      res2(t) = (f(t)-f(p))*(1/(t-p)) (by DifferenceQuotient). Indeed res2(t) = DQ(f,p)(t).
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
  If f is differentiable at p and f has local maxima at p
  then D(f,p)=0.
Proof.
  Assume f is differentiable at p and f has local maxima at p.
  Let us show that there exists del such that x<p-del and p+del<y
      and for any t \in [x|y] if d(t,p)<del then f(t)<=f(p).
    Take positive real number del' such that for any t \in [x|y] if d(t,p)<del' then f(t)<=f(p) (by 5_7a).
    Indeed f has local maxima at p.
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
    Define res1(t) = DQ(f,p)(t) for t in (p-del|p).
    Then res1 is a real map. Indeed DQ(f,p) is a real map.
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
    Take a real map res2 such that res2 is defined on (p|p+del) and
      for every t \in (p|p+del) res2(t) = DQ(f,p)(t) (by RestrictedFunction).
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

# Compactness
# Maybe there is a better definition but this works for now.
Axiom Compactness.
  [x|y] is compact.


Lemma DerivativeOfConstantFunction.
  Let f be a real map that is defined on [x|y].
  Let c be a real number such that for any t \in [x|y] f(t) = c.
  Let p be an element of (x|y).
  Then f is differentiable at p
    and D(f,p) = 0.
Proof.
  DQ(f,p) is a real map that is defined on [x|y]\\{p} (by DifferenceQuotient).
  Let us show that for any t \in [x|y]\\{p} DQ(f,p)(t) = 0.
    Suppose t \in [x|y]\\{p}.
    Then f(t) = c = f(p).
    Then f(t)-f(p) = 0.
    Then (f(t)-f(p)) * (1/(t-p)) = 0.
    Therefore DQ(f,p)(t) = 0 (by DifferenceQuotient).
  End.
  Then lim(DQ(f,p),p)=0 (by LimitOfConstantFunction).
  D(f,p)=0 iff lim(DQ(f,p),p)=0 (by Derivative).
  Therefore D(f,p)=0.
QED.

[prove off]
Lemma ContinuityOfScaledFunction.
  Let f be a real map.
  Let c be a real number.
  Let p be an element of Dom(f) that is an limit point of Dom(f).
  Let f be continuous at p.
  Then c~f is continuous at p.

Lemma DerivativeOfScaledFunction.
  Let f be a real map.
  Let c be a real number.
  Let p be a limit point of Dom(f).
  Let f be differentiable at p.
  Then D(c~f,p) = c * D(f,p).


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
[prove on]
[check on]
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
    h is continuous at t (by 4_9). Indeed h = (c~g)++(d~f).
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
    DQ(h,p) is a real map that is defined on [x|y]\\{p} (by DifferenceQuotient).
    Let us show that for any t \in [x|y]\\{p} DQ(h,p)(t) = 0.
      Assume that t \in [x|y]\\{p}.
      Then h(t)-h(p) = 0. Indeed h(t) = h(x) = h(p).
      (t-p) != 0.
      Then (h(t)-h(p)) * (1/(t-p)) = 0.
      Let us show that DQ(h,p)(t) = 0.
        h is a real map that is defined on [x|y].
        p is an element of (x|y).
        t is an element of Dom(DQ(h,p)).
        Then DQ(h,p)(t) = (h(t)-h(p)) * (1/(t-p)) (by DifferenceQuotient).
        Therefore the thesis.
      End.
    End.
    Let us show that lim(DQ(h,p),p)=0.
      Dom(DQ(h,p)) is a subset of Real.
      Let us show that for any eps there exists del such that for any t \in Dom(DQ(h,p)) if 0<d(t,p)<del then d(DQ(h,p)(t),0)<eps.
        Assume that eps is a positive real number.
        Let us show that for any t \in Dom(DQ(h,p)) if 0<d(t,p)<1 then d(DQ(h,p)(t),0)<eps.
          Assume t \in Dom(DQ(h,p)) and 0<d(t,p)<1.
          Then d(DQ(h,p)(t),0)=0. Indeed DQ(h,p)(t) = 0.
          Then d(DQ(h,p)(t),0)<eps.
        End.
      End.
      Therefore the thesis (by 4_1).
    End.
    Then D(h,p)=0 (by Derivative).
    Therefore the thesis. Indeed there exists t \in (x|y) such that D(h,t)=0.
  End.

  # Case 2: h has a maxima in (x|y).
  Case there exists t \in (x|y) such that h(t) > h(x).
    Let us show that there exists p \in (x|y) such that h has local maxima at p.
      h is continuous.
      Dom(h) is nonempty.
      Dom(h) is compact (by Compactness). Indeed Dom(h) = [x|y].
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
      Let us show that h has local maxima at p.
        1 is a positive real number.
        Let us show that for any t \in Dom(h) if d(t,p)<1 then h(t)<=h(p).
          Assume t \in Dom(h).
          Then h(t)<=h(p).
        End.
        Therefore the thesis (by 5_7b).
      End.
    End.
    Take p \in (x|y) such that h has local maxima at p.
    p is a limit point of Dom(h).
    Let us show that D(h,p)=0.
      h is a real map that is defined on [x|y].
      p is an element of (x|y).
      h is differentiable at p and h has local maxima at p. Indeed h is differentiable on (x|y).
      Therefore the thesis (by 5_8b).
    End.
    Therefore the thesis. Indeed there exists t \in (x|y) such that D(h,t)=0.
  End.

  # Case 3: h has a minima in (x|y).
  Case there exists t \in (x|y) such that h(t) < h(x).
    Let us show that there exists p \in (x|y) such that h has local minima at p.
      h is continuous.
      Dom(h) is nonempty.
      Dom(h) is compact (by Compactness). Indeed Dom(h) = [x|y].
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
      Let us show that h has local minima at p.
        1 is a positive real number.
        Let us show that for any t \in Dom(h) if d(t,p)<1 then h(t)>=h(p).
          Assume t \in Dom(h).
          Then h(t)>=h(p).
        End.
        Therefore the thesis (by 5_7a).
      End.
    End.
    Take p \in (x|y) such that h has local minima at p.
    p is a limit point of Dom(h).
    Let us show that D(h,p)=0.
      h is a real map that is defined on [x|y].
      p is an element of (x|y).
      h is differentiable at p and h has local minima at p. Indeed h is differentiable on (x|y).
      Therefore the thesis (by 5_8a).
    End.
    Therefore the thesis. Indeed there exists t \in (x|y) such that D(h,t)=0.
  End.
  (For any t \in (x|y) h(t) = h(x)) or (there exists t \in (x|y) such that h(t) > h(x))
    or (there exists t \in (x|y) such that h(t) < h(x)).
QED.