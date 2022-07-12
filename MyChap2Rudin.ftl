[synonym number/-s] [synonym sequence/-s] [synonym converge/-s] [synonym function/-s]
[synonym map/-s]
[prove off ][read numbers.ftl] [prove on] #el prove off prove on hace que leas el
# archivo pero no lo pruebes
Definition.A natural number is an integer k such that k=0 or 0<k .
Definition. Let x and y be real numbers. x =< y iff x=y or x<y.
Let m, n, l, r, N denote natural numbers.
Definition. NAT is a set such that every element of NAT is a natural number and every
natural number is an element of NAT.

Signature.Let x be a real number. abs(x) is a real number.
Axiom. Let x be a positive real number. abs(x) = x.
Axiom. abs(0)=0.
Axiom. Let x be a negative real number. abs(x)=-x.
Lemma. For every real number x 0=<abs(x).

Axiom. Let x,y be real numbers.abs(x+y)=< abs(x)+abs(y).

Definition Dist. Let x and y be real numbers. dist(x,y)=abs(x-y).

#We already have the notion of function defined in numbers, there's no point 
#on defining it again. So is the notion of domain.

Lemma. Let f be a function. Ran(f) is a set. #Range of f is also defined.

#I can't write "a map", weird.



Definition ImOfSubset.  Let f be function. Let E be a subset of Dom(f). 
 Im(E,f) = { f(x)  | x is an element of E}.

Definition SurjectiveToB.Let B be a set. Let f be a function.
f is surjective onto B iff Ran(f) = B.

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

Definition Countable. Let A be a set. A is countable iff A and NAT are equipotent. 

Definition FinNAT. Fin(n) = {x | x is a natural number and x=<n}.

Definition Finite. Let A be a set. A is finite iff (A is empty set or there exists n such that A 
and Fin(n) are equipotent). 

Definition Infinite. Let A be a set. A is infinite iff A is not finite. 

Definition Uncountable. Let A be a set. A is uncountable iff (A is not finite and A 
is not countable).

Definition AtMostCount. Let A be a set. A is at most countable iff (A is finite or A is countable).

#Now we introduce sequences, which might be redundant with chapter 3. 

Definition Sequence. A sequence is a function a such that Dom(a) = NAT.

Axiom SubOfCount. Let A be a countable set. Let E be a subset of A. If E is infinite then
E is countable.  #These should be a theorem.

Definition ColOfSets. Let I be a set. For every i element of I let Ei be a set. 
