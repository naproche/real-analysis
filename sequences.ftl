[read real-analysis/vocabulary.ftl]
[read real-analysis/numbers.ftl]

### Preliminaries

Definition. A natural number n is an integer such that n >= 0.

Let n, m, k, N, N1, N2, N3 denote natural numbers.
Let x, y, z denote real numbers.
Let 2 denote 1+1.

Signature. |x| is a real number.
Axiom. If x is positive then |x| = x.
Axiom. If x is negative then |x| = -x.
Axiom. x is 0 iff |x| = 0.
Proposition. Let x be a real number. |x| >= 0.
Proposition. Let x be a real number. |-x| = |x|.

Signature. dist(x,y) is a real number.
Axiom. dist(x,y) = |x - y|.
Proposition. Let x,y be real numbers. |x+y| <= |x| + |y|.
Proof.
Case x+y is positive. Then |x+y| = x+y <= |x| + |y|. end.
Case x+y is negative. 
  |x+y| = -(x+y) = (-x) + (-y) <= |-x| + |-y| = |x| + |y|.
end. qed.

Lemma Trinagle inequality. Let x,y,z be real numbers. Then
dist(x,y) <= dist(x,z) + dist(z,y).
Proof.
dist(x,y) = |x - y| = |(x-z) + (z-y)| <= |x-z| + |z-y| =  dist(x,z) + dist(z,y).
qed.

Lemma. Let x,y be real numbers. dist(x,y) = dist(y,x).
Proof. dist(x,y) = |x - y| = |-(x - y)| = |y - x| = dist(y,x). qed.

Signature. max(x,y) is a real number.
Axiom. If x >= y then max(x,y) = x.  
Axiom. If x < y then max(x,y) = y.
Theorem. max(x,y) >= x and max(x,y) >= y.


### Sequences

Definition Seq.
    A sequence f is a function such that every element of Dom(f) is a natural number and every
    natural number is an element of Dom(f) and for every n f(n) is a real number.

Axiom SequenceEq.
    Let a, b be sequences. a = b iff (for every n a(n) = b(n)).


### Convergence

Definition Convergence.
    Let a be a sequence. Let x be a real number. a converges to x iff for every positive real
    number eps there exists N such that for every n such that N < n |a(n) - x| < eps.

Definition Conv.
    Let a be a sequence. a converges iff there exists a real number x such that a converges to x.

Let a is convergent stand for a converges.
Let a diverges stand for not (a converges).
Let a is divergent stand for a diverges.

### Range

Definition Range.
    Let a be a sequence. ran(a) = {a(n) | n is a natural number}. 

Definition RangeN.
    Let a be a sequence. ranN(a,N) = {a(n) | n is a natural number such that n <= N}.

Definition FiniteRange.
    Let a be a sequence. a has finite range iff there exists an N such that ran(a) = ranN(a,N).

Definition InfiniteRange.
    Let a be a sequence. a has infinite range iff not (a has finite range).


### Sequence 1/n converges to 0 and has infinite range

Lemma. 
    Let a be a sequence such that for every n
        ((If n = 0 then a(n) = 2) and (If n != 0 then a(n) = 1/n)).
    Then a converges to 0 and a has infinite range.
Proof.
    Let us show that a converges to 0.
        Let eps be a positive real number. 
        Take N such that 1 < N * eps.

        Let us show that for every n such that N < n |a(n)| < eps.
          Let n be a natural number such that N < n. Then n != 0.
            Let us show that 1/n < eps.
                We have N * eps < n * eps.
                Hence 1 < n * eps.

                1/n is positive.
                Hence 1/n * 1 < 1/n * (n * eps).
                We have 1/n * 1 = 1/n.
                1/n * (n * eps) = (1/n * n) * eps
                                = 1 * eps 
                                = eps.
            end.
            Hence |a(n)| = 1/n < eps.
         end.
    end.

    Let us show that a has infinite range.
        Assume the contrary.
        Take N such that ran(a) = ranN(a,N).
        Then a(N + 1) is an element of ran(a).

        Let us show that a(N + 1) is not an element of ranN(a,N).
            Let us show that for every n such that n <= N a(n) != a(N + 1).
                Assume the contrary.
                Take n such that n <= N and a(n) = a(N + 1).
                Case n = 0.
                    We have 2 = 1/(N + 1).

                    (2 * N) + 2 .= (2 * N) + (2 * 1)
                                .= 2 * (N + 1)
                                .= 1/(N + 1) * (N + 1)
                                .= 1.

                    We have (2 * N) + 2 > 1.
                    Contradiction.
                end.
                Case n != 0.
                    We have N + 1 != 0.
                    Then 1/n  = 1/(N + 1).
                    Then 1/(1/n) = 1/(1/(N + 1)).
                    Hence n = N + 1.
                    Contradiction.
                end.
            end.
            Hence a(N + 1) is not an element of ranN(a,N).
        end.

        Contradiction.
    end.
qed.

### Sequence (-1)^n diverges and has finite range.

Signature Parity.
    n is even is an atom.

Let n is odd stand for not (n is even).

Axiom ParityPlusOne.
    n is even iff n + 1 is odd.

Axiom ZeroEven. 0 is even.

Lemma OneOdd. 1 is odd.

Lemma.
    Let a be a sequence such that for every n (((n is even) => a(n) = 1) and ((n is odd) => a(n) = -1)).
    Then a diverges and a has finite range.
Proof.
    Let us show that a diverges.
        Assume the contrary.
        Take a real number x such that a converges to x.
        Take N such that for every n such that N < n dist(a(n),x) < 1.

        Let us show that dist(a(N + 1),a(N + 2)) = 2.
            Case N + 1 is even.
                Then (N + 2) is odd.
                Hence dist(a(N + 1),a(N + 2)) = dist(1,-1) = |1+1| = 2.
            end.
            Case N + 1 is odd.
                Then N + 2 is even.
                Hence dist(a(N + 1),a(N + 2)) = dist(-1,1) = |-1-1|= 2.
            end.
        end.

        a(N + 1) is a real number and a(N + 2) is a real number.
        We have dist(a(N + 1),a(N + 2)) <= dist(a(N + 1),x) + dist(x,a(N + 2)).
        We have dist(x,a(N + 2)) = dist(a(N + 2),x).
        Hence dist(a(N + 1),a(N + 2)) <= dist(a(N + 1),x) + dist(a(N + 2),x).

        We have dist(a(N + 1),x) < 1 and dist(a(N + 2),x) < 1.
        Hence dist(a(N + 1),x) + dist(a(N + 2),x) <  dist(a(N + 1),x) + 1 < 1 + 1.
        Hence dist(a(N + 1),a(N + 2)) < 2.
        Hence 2 < 2.
        Contradiction.
    end.

    Let us show that a has finite range.
        Let us show that ran(a) = ranN(a,1).
            Let us show that every element of ranN(a,1) is an element of ran(a).
                Let x be an element of ranN(a,1).
                Take n such that n <= 1 and a(n) = x.
                Hence x is an element of ran(a).
            end.

            Let us show that every element of ran(a) is an element of ranN(a,1).
                Let x be an element of ran(a).

                Let us show that x = 1 or x = -1.
                    Take n such that a(n) = x.
                    n is even or n is odd.
                    Hence x = 1 or x = -1.
                end.

                We have a(0) = 1.
                We have a(1) = -1.

               Case x = 1.
                    Then x = a(0).
                    We have 0 <= 1.
                    Hence x is an element of ranN(a,1).
                end.
                Case x = -1.
                    Then x = a(1).
                    We have 1 <= 1.
                    Hence x is an element of ranN(a,1).
                end.
            end.
        end.
    end.
qed.

### Neighborhood

Definition Neighb.
    Let eps be a positive real number. Let x be a real number.
    Neighb(x,eps) = {y | y is a real number such that dist(y,x) < eps}.

Theorem ConvNeighborhood.
    Let a be a sequence. Let x be a real number.
    a converges to x iff for every positive real number eps there exists a N
    such that for every n such that N < n a(n) is an element of Neighb(x,eps).
Proof.
    Let us show that (If a converges to x then for every positive real number eps there exists a N
    such that for every n such that N < n a(n) is an element of Neighb(x,eps)).
        Assume a converges to x.
        Let eps be a positive real number.
        Take N such that for every n such that N < n dist(a(n),x) < eps.
        Hence for every n such that N < n a(n) is an element of Neighb(x,eps).
    end.
    
    Let us show that (If for every positive real number eps there exists a N such that
    for every n such that N < n a(n) is an element of Neighb(x,eps) then a converges to x).
        Assume for every positive real number eps there exists a N such that
            for every n such that N < n a(n) is an element of Neighb(x,eps).
        Let eps be a positive real number.
        Take N such that for every n such that N < n a(n) is an element of Neighb(x,eps).
        Hence for every n such that N < n dist(a(n),x) < eps (by Neighb).
    end.
qed.



### Limit is unique

Lemma DistEqual.
    Let x and y be real numbers. Assume for every positive real number eps dist(x,y) < eps.
    Then x = y.
Proof.
	Assume the contrary. Then dist(x,y) != 0. |x-y| > 0. Then dist(x,y)//2 is a positive real number. 
	Then dist(x,y)//2 < (dist(x,y)//2) +  (dist(x,y)//2) =  dist(x,y).
   Contradiction.
qed.

Theorem LimitUnique.
    Let a be a sequence. Let x, y be real numbers. Assume a converges to x and a converges to y.
    Then x = y.
Proof.
    Let us show that for every positive real number eps dist(x,y) < eps.
        Let eps be a positive real number.
        Take a positive real number halfeps such that halfeps = 1/2 * eps.

        Take N1 such that for every n such that N1 < n dist(a(n),x) < halfeps.
        Take N2 such that for every n such that N2 < n dist(a(n),y) < halfeps.

        For every n dist(x,y) <= dist(x,a(n)) + dist(a(n),y). 
        Take N3 such that N3 = max(N1,N2) + 1.
        Then N1 < N3 and N2 < N3.

        Hence dist(x,a(N3)) < halfeps and dist(a(N3),y) < halfeps.
        Hence dist(x,a(N3)) + dist(a(N3),y) <  dist(x,a(N3)) + halfeps < halfeps + halfeps.
        Hence dist(x,y) <= dist(x,a(N3)) + dist(a(N3),y) < halfeps + halfeps = eps.
    end.
    Therefore x = y.
qed.

### A convergent sequence is bounded

Definition BoundedBy.
  Let a be a sequence. Let K be a real number. a is bounded by K iff for every n |a(n)|<=K.

Definition BoundedSequence. 
  Let a be a sequence. a is bounded iff there exists a real number K such
  that a is bounded by K.

Signature MaxN.
  Let a be sequence. maxN(a,N) is a real number such that (there exists n such that n<=N and
  maxN(a,N)=a(n)) and (for every n such that n<=N a(n)<=maxN(a,N)). 

Theorem ConvergentImpBounded. 
  Let a be a sequence. Assume that a converges. Then a is bounded.
Proof.
    Take a real number x such that a converges to x.
    Take N such that for every n such that N < n dist(a(n),x) < 1.

    Define b(k) = |a(k)| for k in Natural. b is a sequence.
    Take a real number K such that K = max(1 + |x|, maxN(b,N)).

    Let us show that a is bounded by K.
        Let us show that for every n |a(n)| <= K. 
            Let n be a natural number.
            We have n <= N or n > N.
            Case n <= N.
                We have |a(n)| = b(n) <= maxN(b,N).
                We have maxN(b,N) <= K.
                Therefore |a(n)| <= K.
            end.
            Case n > N.
                We have dist(a(n),x) < 1.
                We have 1 + |x| <= K.

                |a(n)| = |a(n) + 0| = |a(n) + (x - x)| = |(a(n) - x) + x|.

                Hence |a(n)| <= |a(n) - x| + |x|.
                Hence |a(n)| <= dist(a(n),x) + |x|.

                We have dist(a(n),x) + |x| < 1 + |x|.
                Hence |a(n)| <= 1 + |x|.
                Therefore |a(n)| <= K.
            end.
        end.
        Hence a is bounded by K.
    end.
qed.


Definition LimitPointOfSet. 
  Let E be a set. Assume every element of E is a real number. A limit point of E is a real number x
  such that for every positive real number eps there exists an element y of E such that y is an 
  element of Neighb(x,eps) and y !=x.

Theorem ConvLimitPoint.
    Let E be a set. Assume every element of E is a real number. Let x be a limit point of E.
    Then there exists a sequence a such that a converges to x and for every n a(n) is an element of E.
Proof.
    Let us show that for every n such that n > 0 there exists an element y of E such that
    y is an element of Neighb(x,1/n) and y != x.
        Let n be a natural number such that n > 0.
        Then 1/n is a positive real number.
        Take an element y of E such that y is an element of Neighb(x,1/n)
            and y != x.
    end.

    Define a(n) = Case n = 0 -> Choose an element y of E such that y is an element of
                                Neighb(x,1) and y != x in y,
                  Case n > 0 -> Choose an element y of E such that y is an element of
                                Neighb(x,1/n) and y != x in y
    for n in Natural.
    a is a sequence.

    Then for every n a(n) is an element of E.
    Let us show that a converges to x.
        Let eps be a positive real number.
        Take N such that 1 < N * eps.

        Let us show that for every n such that N < n dist(a(n),x) < eps.
            Let n be a natural number such that n > N. Then n != 0.
            Then a(n) is an element of E such that a(n) is an element of Neighb(x,1/n).
            Hence dist(a(n),x) < 1/n.

            Let us show that 1/n < eps.
                We have N * eps < n * eps.
                Hence 1 < n * eps.

                1/n is positive.
                Hence 1/n * 1 < 1/n * (n * eps).
                We have 1/n * 1 = 1/n.
                1/n * (n * eps) .= (1/n * n) * eps
                                   .= 1 * eps
                                   .= eps.
            end.
            Hence dist(a(n),x) < eps.
        end.
    end.
qed.

### Sum and Product of Sequences


Definition SequenceSum.
  Let a,b be sequences. a ++ b is a sequence such that (a++b)(n)=a(n)+b(n) for every n.

Definition SequenceProd.
  Let a,b be sequences. a ** b is a sequence such that (a**b)(n)=a(n)+b(n) for every n.

Definition SequenceConstSum.
  Let a be a sequence. Let c be a real number.
  c+'a is a sequence such that (c+'a)(n)=c+a(n) for every n.

Definition SequenceConstProd.
 Let a be a sequence. Let c be a real number.
 c*'a is a sequence such that (c*'a)(n)=c*a(n) for every n.

Definition SequenceDiv.
  Let a be a sequence. Assume for every n a(n) != 0. div(a) is a sequence such that
  (div(a))(n)=1/a(n) for every n. 

Theorem SumConv.
    Let a,b be sequences. Let x,y be real numbers. Assume a converges to x and b converges to y.
    Then a ++ b converges to x + y.
Proof.
    Let eps be a positive real number.
    Take a positive real number halfeps such that halfeps = 1/2 * eps.

    Take N1 such that for every n such that N1 < n dist(a(n),x) < halfeps (by Convergence).
    Take N2 such that for every n such that N2 < n dist(b(n),y) < halfeps (by Convergence).
    Take N such that N = max(N1,N2).
    Then N1 <= N and N2 <= N.

    Let us show that for every n such that N < n dist((a ++ b)(n),(x+y)) < eps.
        Let n be a natural number such that N < n.
        We have dist(a(n),x) < halfeps.
        We have dist(b(n),y) < halfeps.

        |(a(n) + b(n)) - (x + y)| .= |(a(n) + b(n)) + ((-x) + (-y))|
                                     .= |(-x) + ((a(n) + b(n)) - y)|
                                     .= |(-x) + (a(n) + (b(n) - y))|
                                     .= |((-x) + a(n)) + (b(n) - y)|
                                     .= |(a(n) - x) + (b(n) - y)|.

        We have |(a(n) - x) + (b(n) - y)| <= |a(n) - x| + |b(n) - y|.
        Hence |(a(n) + b(n)) - (x + y)| <= dist(a(n),x) + dist(b(n),y).

        Hence dist(a(n),x) + dist(b(n),y) < halfeps + halfeps = eps.
        Hence |(a(n) + b(n)) - (x + y)| < eps.
        Hence dist((a ++ b)(n),(x + y)) < eps.
    end.
qed.

Lemma ConstConv.
  Let c be a real number. Let cn be a sequence such that for every n cn(n)=c. Then cn converges to c.

Theorem SumConstConv.
  Let a be a sequence. Let x,c be real numbers. Assume a converges to x. Then c+'a converges to c+x.
Proof.
    Define cn(n) = c for n in Natural. cn is a sequence.
    Let us show that c +' a = cn ++ a.
        Let us show that (c +' a)(n) = (cn ++ a)(n) for every natural number n.
            Let n be a natural number.
            (c +' a)(n) .= c + a(n)
                         .= cn(n) + a(n)
                         .= (cn +' a)(n).
        end.
        Hence c +' a = cn ++ a.
    end.
    cn converges to c.
    Then c +' a converges to c + x.
qed.
 
Axiom ProdConstConv.
  Let a be a sequence. Let x,c be real numbers. Assume a converges to x. Then c*'a converges to c*x.


Axiom ConstMultSum.
  Let a,b be sequences. Let x,y be real numbers such that for every n b(n)=y*(a(n)+(-x)).
  Assume a converges to x. Then b converges to 0.

Axiom ProdConv.
  Let a,b be sequences. Let x,y be real numbers. Assume a converges to x and b converges to y.
  Then a**b converges to x*y.

Axiom DivConv.
  Let a be a sequence. Let x be a real number such that x !=0. Assume a converges to x.
  Assume for every n a(n)!=0. Then div(a) converges to 1/x.



### Subsequences

Definition IndexSeq. 
  An index sequence is a sequence i such that (for every n i(n) is a natural number) and 
  (for every n i(n)<i(n+1)).

Definition SubSeq.
  Let a be a sequence and i be an index sequence.
  Subseq(a,i) is a sequence such that for every n Subseq(a,i)(n)=a(i(n)).

Definition ConvSubSeq.
  Let a be a sequence. 
  a has some convergent subsequence iff there exists an index sequence i such that Subseq(a,i) converges.

Axiom IndSucc.
  n<n+1.

Axiom IndPrec.
  Assume n !=0. Then there exists m such that n=m+1.

Axiom IndPlusOne. 
  Assume n<m. Then n+1 <=m.

Axiom SubSeqLeq.
  Let a be a sequence. Let i be an index sequence. Then for every n n<=i(n).

Axiom LimitSubSeq. 
  Let a be a sequence. Let x be a real number. 
  a converges to x iff for every index sequence i Subseq(a,i) converges to x.

Axiom BolzanoWeierstrass.
  Let a be a bounded sequence. Then a has some convergent subsequence.


### Cauchy Sequences

Definition Cauchy.
  A cauchy sequence is a sequence a such that for every positive real number eps there exists N such
  that for every n,m such that (N<n and N<m) dist(a(n),a(m))<eps.

Axiom CauchyBounded.
  Let a be a cauchy sequence. Then a is bounded.

Axiom CauchyConvSubSeq.
  Let a be a cauchy sequence such that a has some convergent subsequence.
  Then a converges.

Axiom RComplete.
  Let a be a sequence. a is cauchy sequence iff a converges.

### Monotonic sequences

Definition MonInc.
  Let a be a sequence. a is monotonically increasing iff (for every n,m such that n<=m a(n)<=a(m)).

Definition MonDec.
  Let a be a sequence. a is monotonically decreasing iff (for every n,m such that n<=m a(n)>=a(m)).

Definition Mon. 
  Let a be a sequence. a is monotonic iff a is monotonically increasing
  or a is monotonically decreasing.

Definition UpperBoundSeq.
  Let a be a bounded sequence. Let K be a real number. K is upper bound of a iff (for every n a(n)<=K).


Definition LeastUpperBoundSeq.
  Let a be a bounded sequence. LeastUpper(a) is a real number K such that (K is an upper bound of a)
  and (for every real number L such that L is an upper bound of a K<=L).

Definition LowerBoundSeq.
  Let a be a bounded sequence. Let K be a real number. K is lower bound of a iff (for every n a(n)>=K).

Definition GreatestLowerBoundSeq.
  Let a be a bounded sequence. GreatestLower(a) is a real number K such that (K is a lower bound of a)
  and (for every real number L such that L is a lower bound of a K>=L).

Axiom MonIncCon. 
  Let a be a monotonically increasing bounded sequence. Then a converges.

Axiom MonCon.
  Let a be a monotonic sequence. a converges iff a is bounded.


Definition BoundedAboveBy.
  Let S be a set. Assume every element of S is a real number. Let b be a real number.
  S is bounded above by b iff for every real number x such that x is an element of S x<=b.

### bounded above -> bounded from up.

Definition BoundedAbove.
  Let S be a set. Assume  every element of S is a real number.
  S is bounded from up iff there exists a real number b such that S is bounded above by b.

Definition BoundedBelowBy.
  Let S be a set. Assume every element of S is a real number. Let b be a real number.
  S is bounded below by b iff for every real number x such that x is an element of S x>=b.

### bounded below -> bounded from down.

Definition BoundedBelow.
  Let S be a set. Assume every element of S is a real number.
  S is bounded from down iff there exists a real number b such that S is bounded below by b.

Definition Sup.
 Let S be a set. Assume that every element of S is a real number.
 Assume that S is bounded from up. Let a be a real number such that
 S is bounded above by a. sup(S) = a iff for every real number b such that
 b < a S is not bounded above by b.

Definition Inf.
  Let S be a set. Assume every element of S is a real
  number. Assume that S is bounded from down. Let a be a real number such that
  S is bounded below by a. inf(S) = a iff for every real number b such that
  b > a S is not bounded below by b.

Definition LimSup.
  Let a be a sequence. Let E be a set such that
  E = {x | x is a real number and there exists an index sequence i such that
  Subseq(a, i) converges to x}. limsup(a) = sup(E) iff E is bounded from up.

Definition LimInf.
   Let a be a sequence. Let E be a set such that
   E = {x | x is a real number and there exists an index sequence i such that
   Subseq(a, i) converges to x}. limsup(a) = inf(E) iff E is bounded from down.