[prove off] [read real-analysis/metric_spaces.ftl] [read real-analysis/Countable_sets.ftl]
 [prove on]

#we are going to try and begin with the definitnion of an open cover and with the general 
#definition of compactness.
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