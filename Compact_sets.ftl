[prove off] [read real-analysis/metric_spaces.ftl][prove on]


#Adding the definitions of finitedness bc for some reason it doesn't read the countable sets file
#we are going to try and begin with the definitnion of an open cover and with the general 
#definition of compactness.
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
Proof.
Let us show that for every open cover  C of K in X there exists a finite subcover of
 K in X with respect to C .
 Let C be an open cover of K in X.
 Define D(a) = Choose an element A of C such that a is an element of A in A for a in K.
 Define DD = {D(a)| a is an element of K}.
 Let us show that DD is finite.
  Take a natural number n such that Fin(n) is bigger than K.
  Take a map f such that Dom(f)= Fin(n) and f is surjective onto K.
  Define g(m) = D(f(m)) for m in Fin(n).
  g is surjective onto DD.
 End.
 Let us show that DD is an open cover of K in X. #It proves this on its own without further specification.
 End.
End.
End.

#The proof of this is obvious but I am unsure how one could write it for a computer.(see above)

# Momentarily I skip 2_33 as I do not think compact relative to... is an important thing.

Signature. Let r be a real number. Half(r) is a real number such that Half(r)+Half(r) = r.
#This was written with a < instead of a = which didn't make much sense since then 0 is an 
#admisible option, which messes the next proof.

Definition IntWithBound. Let X be a set. Let C be a nonempty set such that all elements of C are subsets
of X. Inter(C,X) is  a subset of X such that Inter(C,X) = {x| x is contained in all element of C}.
#We needed to add that C is nonempty to avoid the contradiction.

Theorem 2_34. Let X be a nonempty metric space. Let K be a nonempty subset of X. Suppose 
K is compact in X. K is closed in X.

Proof. 
Let us prove that Compl(K,X) is open in X.
  Let us prove that for every element p of Compl(K,X) p is interior point of Compl(K,X) in X. 
      Let p be an element of Compl(K,X). 
      For every element q of K Half(d(p,q)) is a positive real number.
      Take a set E such that (for every element x of E there is an element q of K such that
      x = Neigh(q,Half(d(p,q)),X)) and (for every element q of K Neigh(q,Half(d(p,q)),X) is an 
      element of E). #The usual set notation does not work for some reason
      Let us prove that E is open cover of K in X. Proof.
          For every element x of E there is an element q of K such that x = Neigh(q,Half(d(p,q)),X).
          Thus for every element x of E x is open in X. Thus for every element x of E x is a subset of X.
          For every element q of K (q is an element of Neigh(q,Half(d(p,q)),X)) and 
          Neigh(q,Half(d(p,q)),X) is an element of E. Thus for every element q of K q is an element of U(E,X).
          Thus K is a subset of U(E,X). End.
      Take a finite subcover F of K in X with respect to E such that F is nonempty.
      #Let I be a set such that (for every element x of I) and (for every element y of F) x is an element
      #of y. #Neither this definition or the one with Inter is working :(.
      #We write it as a comment to be able to write more things in the file.
    End.
  End.
K is closed in X. 
qed. 

#This proof is hard. Naproche is claiming everything to be true.

Theorem 2_35. Let X be a metric space. Let K be a subset of X. Suppose K is compact in X.
Let L be a subset of K such that L is closed in K. L is compact in X.

Axiom 2_37. Let X be a metric space. Let K be a subset of X. Suppose K is compact in X.
Let E be a subset of K. Suppose E is infinite. There exists an element x of X such that x is limit
point of E in X.

# Axiom 2_41. Let E be a subset of Real. For this with the notion of compactness in the reals.
#Here it is defined for arbitrary metric spaces. 
 
#This problem happens again in the following results.