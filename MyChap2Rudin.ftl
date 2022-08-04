[synonym number/-s] [synonym sequence/-s] [synonym converge/-s] [synonym function/-s]
[synonym map/-s]
[prove off ][read numbers.ftl] [prove on] #el prove off prove on hace que leas el
#archivo pero no lo pruebes

Definition.A natural number is an integer k such that k=0 or 0<k .
Definition. Let x and y be real numbers. x =< y iff x=y or x<y.
Let m, n, l, r, N denote natural numbers.
Definition. NAT is a set such that every element of NAT is a natural number and every
natural number is an element of NAT.
Definition. Q is a set such that every element of Q is a rational number and every
rational number is an element of Q.

Axiom WellOrder. Let E be a subset of NAT such that E is nonempty. There exist an element x of E such that
for every element y of E x=<y.
#It is very important to say E nonempty, if not it gives a contradiction.

Definition DifOfSets. Let A and B be sets. (A-B) = {x| x is an element of A such that x is not an
element of B }. #Need it for the theorem on subsets of countable sets.

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

#We already have the notion of function defined in numbers, there's no point 
#on defining it again. So is the notion of domain.

Lemma. Let f be a function. Ran(f) is a set. #Range of f is also defined.
Axiom. Let f be a function. Dom(f) is a set. #this is axiliaty for the moment, but it does not
#yield a contradiction.
#I can't write "a map", weird.

Definition ImOfSubset.  Let f be function. Let E be a subset of Dom(f). 
Im(E,f) is a set such that Im(E,f) = { f(x)  | x is an element of E}.
 #with this def, the image is not a set I added, Im(E,f) is a set but it doesn't seem to fix the 
#problem with the next definition. If instead of the image we write Ran(f) it does work


Definition SurjectiveToB.Let B be a set. Let f be a function.
f is surjective onto B iff Im(Dom(f),f) = B.

Definition Preimage. Let f be a function. Let E be a set such that for every element 
y of E there exists an element x of Dom(f) such that f(x) = y. Then 
ImInv(E,f) = {x | x is an element of Dom(f) and f(x) is an element of E}.

Definition Injective. Let f be a function. f is injective iff for every element x 
of Dom(f) and every element y of Dom(f) (if f(x) = f(y) then x = y).

Definition BijectionToB. Let B be a set. Let f be a function.
f is bijective onto B iff (f is injective and f is surjective onto B).

#Signature. Let A be a set. card(A) is a notion.

#Axiom. Let A and B be sets. (card(A) = card(B)) iff there exists a function f such that (Dom(f) = A
#and f is bijective onto B).

#Maybe it is better not to speak about cardinality but rather define equipotency and work from that.

Definition Equipotency. Let A and B be sets. A and B are equipotent iff there exists a function
f such that (Dom(f)=A and f is bijective onto B).

Definition BiggerSet. Let A and B be sets. A is bigger than B iff there exists a function f such that
(Dom(f)=A and f is surjective onto B). #I tried to incorporate this into the definition of surjective
#but the parser was not allowing me to write "there exist n and a function f..." I don't know why.

Definition Countable. Let A be a set. A is countable iff NAT and A are equipotent.  #the order here
#is important, Naproche does not inmediately recognize this is a reflexive relation.

Definition FinNAT.Fin(n) is a set such that Fin(n) = {x | x is a natural number and x=<n}.

Definition Finite. Let A be a set. A is finite iff ( there exists n such that Fin(n)
is bigger than A). #this makes future proofs easier, since sequences need not to be injective
#and dealing with bijective functions with these definitions can be a pain.

Definition Infinite. Let A be a set. A is infinite iff A is not finite. 

Definition Uncountable. Let A be a set. A is uncountable iff (A is not finite and A 
is not countable).

Definition AtMostCount. Let A be a set. A is at most countable iff (A is finite or A is countable).

#Now we introduce sequences, which might be redundant with chapter 3. 

Definition Sequence. A sequence is a function a such that Dom(a) = NAT.
Definition. Let f be a sequence.(f<<n) is a subset of Ran(f) such that
 (f<<n)= {f(m) | m is an element of NAT and m =< n}. #the order relation for naturals does not 
#seem to work Im going to copy in this document what I had in the natural numbers one. That didnt
#work either... Okay, specifying that m is an elemen of NAT the def works.
#Further note one must specify all this things are sets if not, the notions we have defined for sets 
#i.e. (bigger than, equipotent, etc) yield "unrecognized" type errors.

Lemma. Let f be a sequence. (f<<n) is finite.
Proof.
Let g be a function  such that Dom(g) = Fin(n) and for all element m of Fin(n) g(m)=f(m).
g is surjective onto (f<<n).
Fin(n) is bigger than (f<<n). #this is the definition of finitedness as in line 79 
#Q:why does it not prove finitedness.

End.


Theorem SubOfCount. Let A be a countable set. Let E be a subset of A. If E is infinite then
E is countable. #Indeed, after purging the computer does not know how to prove this.
Proof.
Take a function f such that Dom(f)=NAT and f is bijective onto A.
End.
#Indeed, after purging the computer does not know how to prove this..
#first idea: try to define subsequences and work from that. Difficulty: define restrictions of 
#functions. 


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

Definition IntWithBound. Let X be a set. Let C be a set such that all elements of C are subsets
of X. Int(C,X) is a subset of X such that Int(C,X) = {x| x is contained in all element of C}.

Axiom. Let X be a set. Let C be a set such that all elements of C are subsets
of X and C is countable. If every element of C is countable then U(C,X) is countable.
#This is a theorem that will require proof and that I honestly doubt can be proven in Naproche.

Proposition. Let X be a set. Let C be a set such that all elements of C are subsets
of X and C is at most countable. If every element of C is at most countable then U(C,X) is 
at most countable. #oleeee. This is proven given the above theorem.

#I need to talk about tuples of elements now, how do I do this?
#I can't find anything in the examples about how to work with tuples, maybe it is
#easier I just do it with pairs, the theorem is easily generalized by induction

Signature. A pair is an object x such that x =(u,v) for some objects u,v.

Axiom. Let A be a countable set. Let B = {(a,b)| a and b are elements of A}. B is
countable. #This is a theorem, and must be proven as such. 

#We had to add a definition for the rational numbers similar to the one we aded 
#for the naturals for the following Corollary, which for now we announce as axiom.

Axiom. Q is countable. #is a corollary of the above theorem.

#The following theorem is about the countability of a certain type of sequences

Axiom. Let A = {f| f is a sequence and for every element x of NAT f(x)=0 or f(x)=1}.
A is uncountable.

 