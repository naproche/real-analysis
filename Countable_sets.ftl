[synonym number/-s] [synonym sequence/-s] [synonym converge/-s] [synonym map/-s]
[synonym map/-s]
[prove off ][read real-analysis/numbers.ftl] [prove on]
#Axiom. Let X be a class. X is a set.

#Definitions and axioms about natural numbers that serve as preliminaries.
Definition.A natural number is an integer k such that k=0 or 0<k .
Definition. Let x and y be real numbers. x =< y iff x=y or x<y.
Let m, n, l, r, N denote natural numbers.
Definition. NAT is a set such that every element of NAT is a natural number and every
natural number is an element of NAT.
Axiom. Let k be a natural number. For every natural number n such that n=<k k-n is a 
natural number.

Definition SmallestElement. Let E be a nonempty subset of NAT. The smallest 
element of E is  an element x of E such that for every element y of E x=<y. 
Axiom. Let E be a nonempty subset of NAT. There exists an element x of E such
that x is the smallest element of E.

#Set theoretic and countability definitions.

#Axiom. Let f be a map. Ran(f) is a set. #Range of f is also defined.
#Axiom. Let f be a map. Dom(f) is a set.

Definition DifOfSets. Let A and B be sets.
Dif(A,B) is a subset of A such that Dif(A,B) = {x| x is an element of A and x is
 not an element of B}.

Definition ImOfSubset.  Let f be a map. Let E be a subclass of Dom(f). 
Im(E,f) is a set such that Im(E,f) = { f(x)  | x is an element of E}.

Definition SurjectiveToB.Let B be a set. Let f be a map.
f is surjective onto B iff  Im(Dom(f),f) = B.

Definition Preimage. Let f be a map. Let E be a nonempty subset of Im(Dom(f),f). 
ImInv(E,f) is a nonempty subset  of Dom(f) such that 
ImInv(E,f) = {x | x is an element of Dom(f) and f(x) is an element of E}.

Definition Injective. Let f be a map. f is injective iff for every element x 
of Dom(f) and every element y of Dom(f) (if f(x) = f(y) then x = y).

Definition BijectionToB. Let B be a set. Let f be a map.
f is bijective onto B iff (f is injective and f is surjective onto B).

#Signature. Let A be a set. card(A) is a notion.

#Axiom. Let A and B be sets. (card(A) = card(B)) iff there exists a map f such that (Dom(f) = A
#and f is bijective onto B).

Definition Equipotency. Let A and B be sets. A and B are equipotent iff there exists a map
f such that (Dom(f)=A and f is bijective onto B).

Definition BiggerSet. Let A and B be sets. A is bigger than B iff there exists a map f such that
(Dom(f)=A and f is surjective onto B).

#Definition Countable. Let A be a set. A is countable iff NAT and A are equipotent.

Definition FinNAT.Fin(n) is a set such that Fin(n) = {x | x is a natural number and x<n}.

Definition Finite. Let A be a set. A is finite iff (there exists n such that Fin(n)
is bigger than A) or (A is an empty set).

Lemma. Let n be a natural number. Fin(n) is finite.
Proof.
Define g(m) = m for m in Fin(n).
g is a map.
g is surjective onto Fin(n).
End.

Definition Infinite. Let A be a set. A is infinite iff A is not finite. 

Axiom. Let E be a nonempty finite subset of NAT. There exists an element m of E such that for 
every element k of  E k=<m.

Lemma. NAT is infinite.
Proof.
Assume the contrary.
Take a natural number n such that there exists a map f such that Dom(f) = Fin(n) and 
f is surjective onto NAT.
Take a map f such that Dom(f) = Fin(n) and f is surjective onto NAT.
Take a natural number m such that m is an element of Im(Fin(n),f) and for every element
k of  Im(Fin(n),f) k=<m.
End.

Lemma. Let E be a set. Let F be an empty set. Dif(E,F) = E.

Lemma. Let A be an infinite set. Let B be a finite set. Dif(A,B) is infinite.
Proof.
Case B is empty set. Dif(A,B) = A. End.
Case B is nonempty.
Assume the contrary.
  Case Dif(A,B) is empty set. 
  A is a subset of B.
  Let us show that A is finite.
   Take a natural number n such that there exists a map f such that Dom(f) = Fin(n) and 
   f is surjective onto B.
   Take a map f such that Dom(f) = Fin(n) and f is surjective onto B.
   Take an element a of A.
   Define g(m) = Case f(m) is an element of A -> f(m),
                 Case f(m) is not an element of A -> a
                 for m in Fin(n).
   g is surjective onto A.
   End.
  Contradiction.
  End.
Case Dif(A,B) is nonempty.
  Take a natural number n such that there exists a map f such that Dom(f) = Fin(n) and 
  f is surjective onto B.
  Take a map f such that Dom(f) = Fin(n) and f is surjective onto B.
  Take a natural number m such that there exists a map g such that Dom(g) = Fin(m) and 
  g is surjective onto Dif(A,B).
  Take a map g such that Dom(g) = Fin(m) and g is surjective onto Dif(A,B).
  n+m is a natural number.
  Take l = n+m.
  For every element k of Fin(l) such that  n=<k (k-n) is an element of Fin(m).
  Define h(k) = Case  k<n -> f(k),
                Case n=<k -> g(k-n) 
                for k in Fin(l).
  Let us show that for every element x of A there exists an element  k of Fin(l)
  such that h(k) = x.
  Let x be an element of A.
    Case x is an element of B.
      Take an element k of Fin(n) such that f(k) = x.
      h(k) = x.
    End.
    Case x is an element of Dif(A,B).
      Take an element k of Fin(m) such that g(k) = x.
      k+n is an element of Fin(l).
      (k+n)-n = k + (n-n) = k.
      h(k+n) = g(k) = x.
    End.
  End.
  Take an element a of A.
  Define hh(k) = Case h(k) is an element of A-> h(k),
                 Case h(k) is not an element of A -> a
                 for k in Fin(l).
  hh is surjective onto A.  
  A is finite.
  Contradiction.
End.
End.
End.

Lemma. Let A be a set. If there exists a subset B of A such that B is infinite
then A is infinite.

Definition Countable2. Let A be a set. A is countable iff A is infinite and 
NAT is bigger than A.

Definition Uncountable. Let A be a set. A is uncountable iff (A is not finite and A 
is not countable).

Definition AtMostCount. Let A be a set. A is at most countable iff 
(A is finite or A is countable).

Definition Sequence. A sequence is a map a such that Dom(a) = NAT.

Definition. Let f be a sequence.(f<<n) is a subset of Im(Dom(f),f) such that
 (f<<n)= {f(m) | m is an element of NAT and m < n}.

Lemma. Let f be a sequence. (f<<0) is empty set.

#Axiom Restriction. Let f be a map. Let E be a subset of Dom(f). Then there
#exists a map g such that (Dom(g) = E) and for all element a of E g(a) =f(a). 

Definition Restriction. Let f be a map. Let E be a subset of Dom(f). Res(f,E)
is a map such that Dom(Res(f,E)) = E and for all element a of E
 Res(f,E)(a) =f(a).

Lemma. Let f be a sequence. (f<<n) is finite.
Proof.
Take g= Res(f, Fin(n)).
g is surjective onto (f<<n).
Fin(n) is bigger than (f<<n).
End.

Definition ExtByElm. Let f be a map. Let A be a set such that Dom(f) is 
a subset of A. Let b be an element of Im(Dom(f),f). Ext(f,A,b) is a map such that
Dom(Ext(f,A,b)) = A and (for every element x of Dom(f) Ext(f,A,b)(x) = f(x)) and
(for every element y of Dif(A, Dom(f)) Ext(f,A,b)(y) =b).

Definition Smallf. Let M be a set. Let N be a subset of M. Let f be a sequence
 such that f is surjective onto M. Let x be an element of N. x is smallest  with 
respect to f and M in N iff there exists a natural number n such that f(n) =x and for every
natural number m such that m<n f(n) is not an element of N.

Axiom.Let M be a set. Let N be a nonempty subset of M. Let f be a sequence
 such that f is surjective onto M. There exists an element x of N such that x is smallest with
respect to f and M in N.

#The following def turned out to be unnecessary (and probs flawed) in the end.
#Definition SubOfCountAux. Let f be a map such that Dom(f) = NAT.
 #Let E be an infinite subset of Im(Dom(f),f). Aux(f,E) is a sequence
#such that  (for every element m of NAT  Aux(f,E)(m) = y where
#y is an element of  Dif(E, (Aux(f,E)<<m))  such that y is smallest with respect to f and Im(Dom(f),f)
# in Dif(E, (Aux(f,E)<<m))).

#Definition. Let A be a countable set. Let E be an infinite subset of NAT. Let f be
#a map such that Dom(f) = NAT and f is surjective onto A. N(A,E,f) is a subset of NAT
#such that N(A,E,f) = {x| x is a natural number such that f(x) is an element of E}.

Theorem SubOfCount. Let A be a countable set. Let E be an infinite subset of A.
E is countable. 
Proof.
Take a map f such that Dom(f)=NAT and f is surjective onto A.
Define g(n) =  Choose an element a  of Dif(A,(f<<n))
that is smallest with respect to f and A in Dif(A, (f<<n)) in a
for n in NAT.
g is surjective onto E.
End.

#Alternative proofs that we attempted:
#Proof.
#Take a map f such that Dom(f)=NAT and f is surjective onto A.
#Take g = Aux(f,E).
#Let us show that g is surjective onto E.
#  Let us show that every element of Im(Dom(g),g) is an element of E.
#  g(0) is an element of E.
#  Let us show that for every element m of NAT such that 0<m  g(m) is an element of Dif(E, (Aux(f,E)<<m)).
#    Let m be a natural number such that 0<m.
#    g(m) is not an element of (Aux(f,E)<<m).
#    g(m) is an element of E.
#    End.
#  For every element m of NAT Dif(E, ((Aux(f,E)<<m))) is a subset of E.
#  For every element m of NAT such that 0<m g(m) is an element of E.
#  End.

#  Let us show that every element of E is an element of Im(Dom(g),g).
#  For every element x of E there is an element m of NAT such that f(m)=x.
#  Take an element x such that x is an element of E.
#  Take an element k such that k is an element of NAT and f(k) = x.
  
#  End.
#End.
#End.
#This is the first proof I attempted for the above theorem. It works, but it is kind
#of artificial and is not analogous to the one that Rudin gives. Plus as shown
#in the lemma above, checking surjectivity takes quite some time.
#Take an element a such that a is an element of E.
#Take a map f such that Dom(f)=NAT and f is surjective onto A.
#Take g = Res(f, ImInv(E,f)).
#Take h = Ext(g,NAT,a).3
#g is surjective onto E.  (probably this line is superfluous)
#h is surjective onto E.
#NAT is bigger than E.

Proposition SubOfCountGen. Let A be a countable set. Let E be a subset of A.
 E is at most countable.

#Now the results regarding unions. 

#First attempts to define union/intersection.
#Definition ColecOfSubsets. Let I be a set. A colection indexed by I is a set C such that every
#element of C is a set and C and I are equipotent.

#Definition ArbitraryUnion. Let I be a set. Let C be a colection indexed by I. 
#U(C,I) = {x| x is contained in some element of C}. #For some reason contained works but exist
#an E in C such that x is in E doesn't.

#Definition ArbitraryIntersection. Let I be a set. Let C be a colection indexed by I.
#IN(C,I) = {x| x is contained in all element of C}.

Definition UnionWithBound. Let X be a set. Let C be a set such that all elements of C are subsets
of X. U(C,X) is a subset of X such that U(C,X) =  {x| x is contained in some element of C}.

Axiom UnionOfCount. Let X be a set. Let C be a nonempty set such that all elements of C are subsets
of X and C is at most  countable. If every element of C is countable then U(C,X) is countable. 

Definition NatExtOfSet. Let X be a set. Nat(X) is a set such that 
Nat(X)= {x| x is contained in X or x is contained in NAT}.

#The following lemma was going to be auxiliary to the proof of the next result. Then I realized I 
#needed to replicate the proof of the lemma, rather than using it.
#Lemma. Let A be an at most countable set. There exists a countable set X such that 
#A is a subset of X.
#Proof.
#Case A is countable. End.
#Case A is finite. 
 # Case A is an empty set. 
  #  A is a subset of NAT.
   # Define  f(n) = n for n in NAT. #this defines a map not a function. So I had to change all the definitions to be for maps.
   # f is a map.
   # Dom(f) = NAT.
   # f is surjective onto NAT.
   # NAT is countable. #here we had the problem that, with our definitions, it is not obvious for the computer to show NAT is infinite.
   # End.
 # Case A is nonempty.
 # Take n such that there exists a map f such that Dom(f) = Fin(n) and f is surjective onto A.
 # Define X = {x| x is contained in A or (x is a natural number such that n=<x)}. X is a set.
 # Dif(NAT, Fin(n)) is a subset of X.
 # Dif(NAT, Fin(n)) is infinite.
 # X is infinite.
 # A is a subset of X.
 # Take a map f such that Dom(f) = Fin(n) and f is surjective onto A.
 # Define g(m) = Case m<n -> f(m),
 #               Case n=<m -> m
 #               for m in NAT.
 # g is surjective onto X.
 # X is countable.
 # End.
#End.
#End.

Definition IndexOfA. Let A be a finite set. In(A) is a natural number such that (there exists
 a map f such that Dom(f) = Fin(In(A)) and f is surjective onto A).

Proposition. Let X be a set. Let C be a nonempty set such that all elements of C are subsets
of X and C is at most countable. If every element of C is at most countable then U(C,X) is 
at most countable. 
Proof.
Assume every element A of C is at most countable.
Take  Y = Nat(X).
Define F = {A| A is an element of C and A is finite and nonempty}. 
Define D(A) = Case A is an empty set-> NAT,
              Case A is an element of F -> 
              {x| x is contained in A or (x is a natural number such that In(A)=<x)},
              Case A is infinite -> A
              for A in C.
For every element A of C D(A) is a subset of Y.
Let us show that for every element A of C D(A) is countable.
Let A be an element of C.
Let us show that  D(A) is countable.
Proof.
  Case A is empty set.
    Define  f(n) = n for n in NAT.
    f is a map.
    Dom(f) = NAT.
    f is surjective onto NAT. 
    NAT is countable. 
  End.
  Case A is infinite.
  End.
  Case A is an element of F.
    Dif(NAT, Fin(In(A))) is a subset of D(A).
    Dif(NAT, Fin(In(A))) is infinite.
    D(A) is infinite.
    Take a map f such that Dom(f) = Fin(In(A)) and f is surjective onto A.
    Define g(m) = Case m<In(A) -> f(m),
                 Case In(A)=<m -> m
                 for m in NAT.
    Im(Dom(g),g) is a subset of D(A).
    Let us show that every element of D(A) is an element of Im(Dom(g),g).
      Let x be an element of D(A).
      Case x is an element of A. 
        Take a natural number m such that m is an element of Fin(In(A)) and f(m) =x.
         m is an element of Dom(g).
         g(m) =x.
         x is an element of Im(Dom(g),g).
      End.
    End.
    D(A) is a subset of Im(Dom(g),g).
    g is surjective onto D(A).
    D(A) is countable.
  End.
End.
End.
Take CC = Im(C,D).
Let us show that CC is at most countable. 
 Case C is finite. 
  Take a natural number n such that there exists a map g such that Dom(g) = Fin(n) and
  g is surjective onto C.
  Take a map g such that Dom(g) = Fin(n) and g is surjective onto C.
   Let us show that for every element m of Fin(n) g(m) is an element of C.
   Let m be an element of Fin(n).
   g(m) is an element of Im(Fin(n), g).
   Im(Fin(n),g) =C.
   g(m) is an element of C.
   End.
   Define gg(m) = D(g(m)) for m in Fin(n).
   gg is surjective onto CC.
   CC is finite.
 End.
 Case C is countable.
 Case CC is finite. End.
 Case CC is infinite.
  Take a map h such that Dom(h) = NAT and h is surjective onto C.
  Let us show that for every natural number m h(m) is an element of C.
   Let m be a natural number.
   h(m) is an element of Im(NAT, h).
   Im(NAT,h) =C.
   h(m) is an element of C.
   End.
  Define hh(m) = D(h(m)) for m in NAT. 
  hh is surjective onto CC.
  End.
  End.
End.
CC is at most countable.
Every element of CC is a subset of Y.
Every element of CC is countable.
CC is nonempty.
U(CC,Y) is countable.
U(C,X) is a subset of U(CC, Y).
  Let us show that U(C,X) is at most countable.
    Case U(C,X) is finite. End.
    Case U(C,X) is infinite. End.
  End.
End.

#Finally some results regarding pairs and countability of binary senquences.

Signature. A pair x is an object such that x = (u,v) for some objects u,v.

#Theorem. Let A and B be a countable sets.
#A \times B is countable. #This is a theorem, and must be proven as such. 
#Proof.
#Define D(a)  = {(a,b)| b is contained in B} for a in A.

#End. (Commented out since this definition of D(a) does not work).

Axiom. Rational is countable.

Definition. Let f be a sequence such that (for every element n of NAT f(n) = 0 or f(n) = 1). 
S(f) is a sequence such that (for every natural number n such that f(n) = 0 S(f)(n) = 1) and
(for every natural number n such that f(n)=1 S(f)(n)=0).

Definition . Let f be a sequence.  f is  binary  iff for every natural number n
(f(n)=0 or f(n)=1).

Let f is  binary sequence stand for f is a sequence such that f is binary. #again problem with writing a

Definition. Bin is a set such that every element f of Bin is a binary sequence and 
every binary sequence is an element of Bin.

Lemma. Bin is nonempty.
Proof.
Define g(n) = 0 for n in NAT.
End.

Lemma. Bin is infinite.
Proof.
Assume the contrary.
Take a natural number n such that Fin(n) is bigger than Bin.
Take a map f such that Dom(f) = Fin(n) and f is surjective onto Bin.
Let us show that for every element m of Fin(n) f(m)  is an element of Bin.
  Let m  be an element of Fin(n).
  m is an element of Dom(f).
  f(m) is an element of Im(Dom(f),f).
End.
Define g(k) = Case k<n -> S(f(k))(k),
              Case n<=k -> 0
              for k in NAT.
Let us show that for every natural number m (g(m) = 0 or g(m) = 1).
  Let m be a natural number.
  Case n<=m.
  End.
  Case m<n.
  g(m) = S(f(m))(m).
  End.
End.
Let us show that for every element h of Bin h!=g.
  Let h be an element of Bin.
  Take an element m of Fin(n) such that f(m) = h.
End.
End.

Theorem. Bin is uncountable.
Proof.
Assume the contrary. 
Bin is countable.
Take a map f such that Dom(f) = NAT and f is surjective onto Bin.
Let us show that for every natural number n f(n) is an element of Bin.
  Let n be a natural number.
  n is an element of Dom(f).
  f(n) is an element of Im(Dom(f),f).
End.
Define g(n) = S(f(n))(n) for n in NAT.
Let us show that g is an element of Bin.
g is a sequence.
For every natural number n (g(n) = 0 or g(n) = 1).
g is a binary sequence.
End.
Let us show that for every element h of Bin h!=g.
  Let h be an element of Bin.
  Take a natural number n such that f(n) = h.
End.
End.

Definition IntWithBound. Let X be a set. Let C be a nonempty set such that all elements of C are subsets
of X. Inter(C,X) is  a subset of X such that Inter(C,X) = {x| x is contained in all element of C}.