[prove off]
[read preliminaries.ftl]
[read real-analysis/numbers.ftl]
[read real-analysis/Chapter5/differentiation_pre.ftl]
[prove on]

Let x,y,z denote real numbers.
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

Lemma.
  Let S be closed interval. 
  S is nonempty subset of Real and
  S is bounded above and
  S is bounded below.


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


Theorem.
  Let f be a real map such that f is defined on [x|y].
  Let z be an element of (x|y).
  If f is differentiable at z in x and y
  then f is continuous at z.