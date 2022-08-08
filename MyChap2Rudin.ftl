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

#We already have the notion of function defined in numbers, there's no point 
#on defining it again. So is the notion of domain.

Lemma. Let f be a function. Ran(f) is a set. #Range of f is also defined.
Axiom. Let f be a function. Dom(f) is a set. #this is auxiliary for the moment, but it does not
#yield a contradiction.
#I can't write "a map", weird.

Definition ImOfSubset.  Let f be function. Let E be a subset of Dom(f). 
Im(E,f) is a subset of Ran(f) such that Im(E,f) = { f(x)  | x is an element of E}.
 #with this def, the image is not a set I added, Im(E,f) is a set but it doesn't seem to fix the 
#problem with the next definition. If instead of the image we write Ran(f) it does work


Definition SurjectiveToB.Let B be a set. Let f be a function.
f is surjective onto B iff Im(Dom(f),f) = B.

Definition Preimage. Let f be a function. Let E be a nonempty subset of Ran(f). 
ImInv(E,f) is a nonempty subset  of Dom(f) such that #we need this detail to ensure this is a set and that it is nonempty.
#we could have it to be empty, but it is of no use to us and complicates def
#like the def of Aux we need for the theorem on subsets of countable sets.
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

#Definition Countable. Let A be a set. A is countable iff NAT and A are equipotent.  #the order here
#is important, Naproche does not inmediately recognize this is a reflexive relation.


Definition FinNAT.Fin(n) is a set such that Fin(n) = {x | x is a natural number and x<n}.

Definition Finite. Let A be a set. A is finite iff (there exists n such that Fin(n)
is bigger than A) or (A is an empty set). #this makes future proofs easier, since sequences need not to be injective
#and dealing with bijective functions with these definitions can be a pain.

Definition Infinite. Let A be a set. A is infinite iff A is not finite. 

#This is something we will need later on. I put it as an axiom bc it is somewhat obvious but, proving 
#it formally is a pain with these definitions.
Axiom. Let A be an infinite set. Let B be a finite set. Dif(A,B) is infinite.

Definition Countable2. Let A be a set. A is countable iff A is infinite and 
NAT is bigger than A.#this def of countability through surjections is (probably)
#easier to check in the proofs but requires the notion of finitedness, which the
#other one didn't. Also it is not as natural.

Definition Uncountable. Let A be a set. A is uncountable iff (A is not finite and A 
is not countable).

Definition AtMostCount. Let A be a set. A is at most countable iff (A is finite or A is countable).

#Now we introduce sequences, which might be redundant with chapter 3. 

Definition Sequence. A sequence is a function a such that Dom(a) = NAT.
Definition. Let f be a sequence.(f<<n) is a subset of Ran(f) such that
 (f<<n)= {f(m) | m is an element of NAT and m < n}. #the order relation for naturals does not 
#seem to work Im going to copy in this document what I had in the natural numbers one. That didnt
#work either... Okay, specifying that m is an elemen of NAT the def works.
#Further note one must specify all this things are sets if not, the notions we have defined for sets 
#i.e. (bigger than, equipotent, etc) yield "unrecognized" type errors.

#First idea to go through with the problem of defining g in the lemma:
# define restriction of a function.

#Axiom Restriction. Let f be a function. Let E be a subset of Dom(f). Then there
#exists a function g such that (Dom(g) = E) and for all element a of E g(a) =f(a). 
#Writing this does not work in the proof bc we don't use f when taking the function
#g in the proof, so it does not work. To solve this we define the restriction to
#give it a name.

Definition Restriction. Let f be a function. Let E be a subset of Dom(f). Res(f,E)
is a function such that Dom(Res(f,E)) = E and for all element a of E
 Res(f,E)(a) =f(a). #with this definition, the lemma works.

Lemma. Let f be a sequence. (f<<n) is finite.
Proof.
Take g= Res(f, Fin(n)).
g is surjective onto (f<<n).
Fin(n) is bigger than (f<<n). #this is the definition of finitedness as in line 79 
#Q:why does it not prove finitedness if i say let g be a function...
#. A: using "let g be a function..." does not
#build the function.
#The part of proving that g is surjective takes a while but Naproche can do it on its own.
End.
#These are definitions I wish I could type directly into the proofs, but i don\<acute>t know how.
Definition ExtByElm. Let f be a function. Let A be a set such that Dom(f) is 
a subset of A. Let b be an element of Ran(f). Ext(f,A,b) is a function such that
Dom(Ext(f,A,b)) = A and (for every element x of Dom(f) Ext(f,A,b)(x) = f(x)) and
(for every element y of Dif(A, Dom(f)) Ext(f,A,b)(y) =b).

Definition SubOfCountAux. Let f be a function such that Dom(f) = NAT.
 Let E be an infinite subset of Ran(f). Aux(f,E) is a function such
that Dom(Aux(f,E)) = NAT and (Aux(f,E)(0) = f(x) where x is smallest element
 of ImInv(E,f)) and (for every element m of NAT such that 0<m Aux(f,E)(m) = f(y) where
y is the smallest element of ImInv(Dif(E, (Aux(f,E)<<m)),f)).
#We need to make the machine understand that ImInv(E,f) is not empty, which is 
#apparently not direct from the definition.(Now that I have modified the definition, it is)
#Note: to make this work I had to change the =< in the defs of Fin(n) and (f<<n) since we 
#do not have a symbol for the previous element.

Theorem SubOfCount. Let A be a countable set. Let E be an infinite subset of A.
E is countable. #Indeed, after purging the computer does not know how to prove this.
Proof.
Take a function f such that Dom(f)=NAT and f is surjective onto A.
Take g = Aux(f,E).
g is surjective onto E.
End.
#Indeed, after purging the computer does not know how to prove this..
#first idea: try to define subsequences and work from that. Difficulty: define restrictions of 
#functions. 

#This is the first proof I attempted for the above theorem. It works, but it is kind
#of artificial and is not analogous to the one that Rudin gives. Plus as shown
#in the lemma above, checking surjectivity takes quite some time.
#Take an element a such that a is an element of E.
#Take a function f such that Dom(f)=NAT and f is surjective onto A.
#Take g = Res(f, ImInv(E,f)).
#Take h = Ext(g,NAT,a).3
#g is surjective onto E.  (probably this line is superfluous)
#h is surjective onto E.
#NAT is bigger than E.

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

