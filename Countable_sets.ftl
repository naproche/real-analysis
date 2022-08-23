[synonym number/-s] [synonym sequence/-s] [synonym converge/-s] [synonym map/-s]
[synonym map/-s]
[prove off ][read real-analysis/numbers.ftl] [prove on]
 #el prove off prove on hace que leas el archivo pero no lo pruebes.
#Axiom. Let X be a class. X is a set. #we are going to work only with sets, and I can't define
#sets inside theorems, only classes. This is false, but we only need to redefine CC in the
#looong proof the rest works fine.


Definition.A natural number is an integer k such that k=0 or 0<k .
Definition. Let x and y be real numbers. x =< y iff x=y or x<y.
Let m, n, l, r, N denote natural numbers.
Definition. NAT is a set such that every element of NAT is a natural number and every
natural number is an element of NAT.
Definition. Q is a set such that every element of Q is a rational number and every
rational number is an element of Q.
Axiom. Let k be a natural number. For every natural number n such that n=<k k-n is a 
natural number.

Definition SmallestElement. Let E be a nonempty subset of NAT. The smallest 
element of E is  an element x of E such that for every element y of E x=<y. 
Axiom. Let E be a nonempty subset of NAT. There exists an element x of E such
that x is the smallest element of E.
#It is very important to say E nonempty, if not it gives a contradiction.

Definition DifOfSets. Let A and B be sets.
Dif(A,B) is a subset of A such that Dif(A,B) = {x| x is an element of A and x is
 not an element of B}. #Need it for the theorem on subsets of countable sets.
#Note that even saying that it is a subset of A, we need to reference A again
#in the bracket. Otherwise the definition is flawed and yields a contradiction.


#This is just a definition for the distance in R, not strictly necessary for
# the rest of this document.
Signature.Let x be a real number. abs(x) is a real number.
Axiom. Let x be a positive real number. abs(x) = x.
Axiom. abs(0)=0.
Axiom. Let x be a negative real number. abs(x)=-x.
Lemma. For every real number x 0=<abs(x).
#Axiom GoodOrder. For every subset E of NAT there exists an element x of E such that for every 
#element y of E x=<y. This introduces a contradiction but I don't know why??
Axiom. Let x,y be real numbers.abs(x+y)=< abs(x)+abs(y).

Definition Dist. Let x and y be real numbers. dist(x,y)=abs(x-y).

#We already have the notion of map defined in numbers, there's no point 
#on defining it again. So is the notion of domain.

#Axiom. Let f be a map. Ran(f) is a set. #Range of f is also defined.
Axiom. Let f be a map. Dom(f) is a set. #this is auxiliary for the moment, but it does not
#yield a contradiction.
#I can't write "a map", weird. Had to change all functions to maps.

Definition ImOfSubset.  Let f be a map. Let E be a subset of Dom(f). 
Im(E,f) is a set such that Im(E,f) = { f(x)  | x is an element of E}.
 #with this def, the image is not a set I added, Im(E,f) is a set but it doesn't seem to fix the 
#problem with the next definition. If instead of the image we write Ran(f) it does work


Definition SurjectiveToB.Let B be a set. Let f be a map.
f is surjective onto B iff  Im(Dom(f),f) = B.

Definition Preimage. Let f be a map. Let E be a nonempty subset of Im(Dom(f),f). 
ImInv(E,f) is a nonempty subset  of Dom(f) such that #we need this detail to ensure this is a set and that it is nonempty.
#we could have it to be empty, but it is of no use to us and complicates def
#like the def of Aux we need for the theorem on subsets of countable sets.
ImInv(E,f) = {x | x is an element of Dom(f) and f(x) is an element of E}.

Definition Injective. Let f be a map. f is injective iff for every element x 
of Dom(f) and every element y of Dom(f) (if f(x) = f(y) then x = y).

Definition BijectionToB. Let B be a set. Let f be a map.
f is bijective onto B iff (f is injective and f is surjective onto B).

#Signature. Let A be a set. card(A) is a notion.

#Axiom. Let A and B be sets. (card(A) = card(B)) iff there exists a map f such that (Dom(f) = A
#and f is bijective onto B).

#Maybe it is better not to speak about cardinality but rather define equipotency and work from that.

Definition Equipotency. Let A and B be sets. A and B are equipotent iff there exists a map
f such that (Dom(f)=A and f is bijective onto B).

Definition BiggerSet. Let A and B be sets. A is bigger than B iff there exists a map f such that
(Dom(f)=A and f is surjective onto B). #I tried to incorporate this into the definition of surjective
#but the parser was not allowing me to write "there exist n and a map f..." I don't know why.

#Definition Countable. Let A be a set. A is countable iff NAT and A are equipotent.  #the order here
#is important, Naproche does not inmediately recognize this is a reflexive relation.


Definition FinNAT.Fin(n) is a set such that Fin(n) = {x | x is a natural number and x<n}.

Definition Finite. Let A be a set. A is finite iff (there exists n such that Fin(n)
is bigger than A) or (A is an empty set). #this makes future proofs easier, since sequences need not to be injective
#and dealing with bijective maps with these definitions can be a pain.

Lemma. Let n be a natural number. Fin(n) is finite.
Proof.
Define g(m) = m for m in Fin(n).
g is a map.
g is surjective onto Fin(n).
End.

Definition Infinite. Let A be a set. A is infinite iff A is not finite. 

Axiom. Let E be a nonempty finite subset of NAT. There exists an element m of E such that for 
every element k of  E k=<m.
#I needed to add this axiom in order to prove the below theorem. 


Lemma. NAT is infinite.
Proof.
Assume the contrary.
Take a natural number n such that there exists a map f such that Dom(f) = Fin(n) and 
f is surjective onto NAT.
Take a map f such that Dom(f) = Fin(n) and f is surjective onto NAT.
Take a natural number m such that m is an element of Im(Fin(n),f) and for every element
k of  Im(Fin(n),f) k=<m.
End.
 #I will revisit this, but it is obvious although hard to prove with this definitions.
#This is something we will need later on. I put it as an axiom bc it is somewhat obvious but, proving 
#it formally is a pain with these definitions.  Adding the above axiom it is proven 
# quite fast. We don\<acute>t even need to write a full proof. However we do need to write some
#steps of the proof.

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
                Case n=<k -> g(k-n) #we need to say that k-n is an element of Fin(m) explcitely
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
  hh is surjective onto A. #h does not go into A we need to restrict it. 
  A is finite.
  Contradiction.
End.
End.
End.

Lemma. Let A be a set. If there exists a subset B of A such that B is infinite
then A is infinite.

#These two are written as axioms bc proving this things with our definition of can be tricky, 
#I'll come back to them.
#I came back, the first lemma took some work, but this second works on its own.

Definition Countable2. Let A be a set. A is countable iff A is infinite and 
NAT is bigger than A.#this def of countability through surjections is (probably)
#easier to check in the proofs but requires the notion of finitedness, which the
#other one didn't. Also it is not as natural.

Definition Uncountable. Let A be a set. A is uncountable iff (A is not finite and A 
is not countable).

Definition AtMostCount. Let A be a set. A is at most countable iff (A is finite or A is countable).

#Now we introduce sequences, which might be redundant with chapter 3. 

Definition Sequence. A sequence is a map a such that Dom(a) = NAT.
Definition. Let f be a sequence.(f<<n) is a subset of Im(Dom(f),f) such that
 (f<<n)= {f(m) | m is an element of NAT and m < n}. #the order relation for naturals does not 
#seem to work Im going to copy in this document what I had in the natural numbers one. That didnt
#work either... Okay, specifying that m is an elemen of NAT the def works.
#Further note one must specify all this things are sets if not, the notions we have defined for sets 
#i.e. (bigger than, equipotent, etc) yield "unrecognized" type errors.
Lemma. Let f be a sequence. (f<<0) is empty set.#Added this axiom to simplify the def of smallest
#wrt f in N.
#First idea to go through with the problem of defining g in the lemma:
# define restriction of a map.

#Axiom Restriction. Let f be a map. Let E be a subset of Dom(f). Then there
#exists a map g such that (Dom(g) = E) and for all element a of E g(a) =f(a). 
#Writing this does not work in the proof bc we don't use f when taking the map
#g in the proof, so it does not work. To solve this we define the restriction to
#give it a name.

Definition Restriction. Let f be a map. Let E be a subset of Dom(f). Res(f,E)
is a map such that Dom(Res(f,E)) = E and for all element a of E
 Res(f,E)(a) =f(a). #with this definition, the lemma works.

Lemma. Let f be a sequence. (f<<n) is finite.
Proof.
Take g= Res(f, Fin(n)).
g is surjective onto (f<<n).
Fin(n) is bigger than (f<<n). #this is the definition of finitedness as in line 79 
#Q:why does it not prove finitedness if i say let g be a map...
#. A: using "let g be a map..." does not
#build the map.
#The part of proving that g is surjective takes a while but Naproche can do it on its own.
End.
#These are definitions I wish I could type directly into the proofs, but i don\<acute>t know how.
Definition ExtByElm. Let f be a map. Let A be a set such that Dom(f) is 
a subset of A. Let b be an element of Im(Dom(f),f). Ext(f,A,b) is a map such that
Dom(Ext(f,A,b)) = A and (for every element x of Dom(f) Ext(f,A,b)(x) = f(x)) and
(for every element y of Dif(A, Dom(f)) Ext(f,A,b)(y) =b).

#For Rudin's proof we need the following two definitions

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
#We need to make the machine understand that ImInv(E,f) is not empty, which is 
#apparently not direct from the definition.(Now that I have modified the definition, it is)
#Note: to make this work I had to change the =< in the defs of Fin(n) and (f<<n) since we 
#do not have a symbol for the previous element.

Definition. Let A be a countable set. Let E be an infinite subset of NAT. Let f be
a map such that Dom(f) = NAT and f is surjective onto A. N(A,E,f) is a subset of NAT
such that N(A,E,f) = {x| x is a natural number such that f(x) is an element of E}.

Theorem SubOfCount. Let A be a countable set. Let E be an infinite subset of A.
E is countable. #Indeed, after purging the computer does not know how to prove this.
Proof.
Take a map f such that Dom(f)=NAT and f is surjective onto A.
Define g(n) =  Choose an element a  of Dif(A,(f<<n))
that is smallest with respect to f and A in Dif(A, (f<<n)) in a
for n in NAT.
g is surjective onto E.
End.
#This proof had a problem with the fact that the def of th Aux function is flawed. However it
#is not needed and, as shown, a much shorter proof can be given.
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
# For the moment I'll leave it as an axiom and go back to it later. The def of Aux(f,E) is n
#not working and I have no clue why.

#Indeed, after purging the computer does not know how to prove this..
#first idea: try to define subsequences and work from that. Difficulty: define restrictions of 
#maps. 

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

#Now we add a simple corolary to this result.

Proposition SubOfCountGen. Let A be a countable set. Let E be a subset of A.
 E is at most countable. #Obviously this comes directly from the above result.

#Definition ColecOfSubsets. Let I be a set. A colection indexed by I is a set C such that every
#element of C is a set and C and I are equipotent.

#Definition ArbitraryUnion. Let I be a set. Let C be a colection indexed by I. 
#U(C,I) = {x| x is contained in some element of C}. #For some reason contained works but exist
#an E in C such that x is in E doesn't.

#Definition ArbitraryIntersection. Let I be a set. Let C be a colection indexed by I.
#IN(C,I) = {x| x is contained in all element of C}.

Definition Disjoint. Let A and B be sets. A is disjoint from B iff there is no 
element of A that is an element of B.

#Since we are actually going to work with the reals, there is a cleaner way to work with this 
# that frees us to check things like the union being a set.

Definition UnionWithBound. Let X be a set. Let C be a set such that all elements of C are subsets
of X. U(C,X) is a subset of X such that U(C,X) =  {x| x is contained in some element of C}.

#Definition IntWithBound. Let X be a set. Let C be a set such that all elements of C are subsets
#of X. Int(C,X) is a subset of X such that Int(C,X) = {x| x is contained in all element of C}.
#the above definition is commented out because it yields a contradiction.

Axiom UnionOfCount. Let X be a set. Let C be a nonempty set such that all elements of C are subsets
of X and C is at most  countable. If every element of C is countable then U(C,X) is countable. 
#the hypothesis C at most countable yields a contradiction, honestly, what on earth... I had to exclude the case where C was empty.
#This is a theorem that will require proof and that I honestly doubt can be proven in Naproche.

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
#Tried to write this definition inside the proof, but was unable. Some syntax error I could not identify.

#In this proposition I exclude the possibility of C being empty. It's trivial to the reader but considering it overcomplicates the proof even further.
Proposition. Let X be a set. Let C be a nonempty set such that all elements of C are subsets
of X and C is at most countable. If every element of C is at most countable then U(C,X) is 
at most countable. # This is proven given the above theorem.Ok it is actually not.
Proof.
Assume every element A of C is at most countable.
Take  Y = Nat(X).
Define F = {A| A is an element of C and A is finite and nonempty}. #this was called Fin at the beggining, bad move on my part, it classes with the Fin(n) sets.
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
Take CC = Im(C,D).#With the definition we have given of D(A) CC might be finite even if C is not. Think if all of the elements of C were finite.
Let us show that CC is at most countable. #We have here the problem that C is at most countable, not necesarilly countable, I'll change the statement of the theorem for the moment
 Case C is finite. 
  Take a natural number n such that there exists a map g such that Dom(g) = Fin(n) and
  g is surjective onto C.
  Take a map g such that Dom(g) = Fin(n) and g is surjective onto C.
   Let us show that for every element m of Fin(n) g(m) is an element of C.
   Let m be an element of Fin(n).# Naproche is unable to show h(m) is an element of C, I'll add it as part of the surjective definition. That was a bad idea, makes proving a map is surjective way harder.
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
   Let m be a natural number.# Naproche is unable to show h(m) is an element of C, I'll add it as part of the surjective definition. That was a bad idea, makes proving a map is surjective way harder.
   h(m) is an element of Im(NAT, h).
   Im(NAT,h) =C.
   h(m) is an element of C.
   End.
  Define hh(m) = D(h(m)) for m in NAT. #We had to prove manually that h(m) is an element of C in order to make this def work.
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

#I need to talk about tuples of elements now, how do I do this?
#I can't find anything in the examples about how to work with tuples, maybe it is
#easier I just do it with pairs, the theorem is easily generalized by induction

Signature. A pair x is an object such that x = (u,v) for some objects u,v.
#writing this as Signature. A pair x is an object such that x = (u,v) where u and v are objects. yields a contradiction. I'm oblivious to why.

Theorem. Let A and B be a countable sets.
A \times B is countable. #This is a theorem, and must be proven as such. 
Proof.
Define D(a)  = {(a,b)| b is contained in B} for a in A.

End.

# Writing  C = {(a,b)| a is contained in A and b is contained in B}. has the problem that Naproche cannot prove C is not empty.

#We had to add a definition for the rational numbers similar to the one we added 
#for the naturals for the following Corollary, which for now we announce as axiom.

Axiom. Q is countable. #is a corollary of the above theorem.

#The following theorem is about the countability of a certain type of sequences

Axiom. Let A = {f| f is a sequence and for every element x of NAT f(x)=0 or f(x)=1}.
A is uncountable.

