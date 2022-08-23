[prove off] [read real-analysis/metric_spaces.ftl][prove on]

#we are going to try and begin with the definitnion of an open cover and with the general 
#definition of compactness.

Definition UnionWithBound. Let X be a set. Let C be a set such that all elements of C are subsets
of X. U(C,X) is a subset of X such that U(C,X) =  {x| x is contained in some element of C}.

#This was added since I deleted, momentarily, reading Countable sets as I was getting an error
#with an invalid naming for the natural numbers????

Definition OpenCover. Let X be a metric space. Let E be a subset of X.An open cover of E in X 
is a set C such that every element of C is a subset of X and every element of C is open in X
and E is a subset of U(C,X).
#The "in X" is necesary as if we don't write it Naproche identifies X as a "free undeclared" variable.

Definition Subcover. Let X be a metric space. Let E be a subset of X. Let C be an open cover of
E in X. A subcover of E in X with respect to C is a subset D of C such that D is an open cover
of E in X.
#Note: In the def of open cover we started with the following format: "Let C be a set such that 
#all its elements are subsets of X. C is an open cover iff..." This lead to the problem that
#when in the next definition I wrote "Let C be an open cover of E in X" it didn't work. 
#Open cover was defined as a property rather than an object. 

Definition Compact. Let X be a metric space. Let K be a subset of X. K is compact in X iff for
every open cover C of K in X there exists a finite subcover of K in X with respect to C . 

#Definition Compactness. Let X be a metric space. Let K be a subset of X. K is compact in X  iff
#for every open cover of K in X  

Lemma. Let X be a metric space. Let K be a finite subset of X. K is compact in X.

#The proof of this is obvious but I am unsure how one could write it for a computer.

# Momentarily I skip 2_33 as I do not think compact relative to... is an important thing.

Signature. Let r be a real number. Half(r) is a real number such that Half(r)+Half(r) < r.


Theorem 2_34. Let X be a nonempty metric space. Let K be a nonempty subset of X. Suppose 
K is compact in X. K is closed in X.

Proof. Let us prove that Compl(K,X) is open in X. Proof. Let us prove that for every element p of
Compl(K,X) p is interior point of Compl(K,X) in X. Proof. 
Let p be an element of Compl(K,X). For every element q of K Half(d(p,q)) is a positive real number.
Let E be a set such that for every element x of E there is an element q of K such that
x = Neigh(q,Half(d(p,q)),X). E is open cover of K in X. #From here i don't know how
#to write a subcover.
End. End.
K is closed in X. qed. 

#This proof is hard. Naproche is claiming everything to be true.

Theorem 2_35. Let X be a metric space. Let K be a subset of X. Suppose K is compact in X.
Let L be a subset of K such that L is closed in K. L is compact in X.

#Theorem 2_37. Let X be a metric space. Let K be a subset of X. Suppose K is compact in X.
#Let E be a subset of K. 
 
#So far I cannot write infinite, as I need the definition of Natural number which for some reason
#Naproche claims to be illegal.