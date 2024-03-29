[read real-analysis/vocabulary.ftl]
[read real-analysis/numbers.ftl]

### Preliminaries

Definition. A natural number n is an integer such that n >= 0.

Definition. NN is the collection of natural numbers.
Theorem. NN is a set.

Let n, m, k, N, N1, N2, N3 denote natural numbers.
Let x, y, z denote real numbers.
Let 2 denote (1+1).
Proposition. Let x be a real number. (1/2*x) + (1/2*x) = x.
Proof. 2*(1/2 + 1/2) = (2*(1/2)) + (2*(1/2)) = 2 = 2*1.
qed.

Signature. |x| is a real number.
Axiom. If x is positive then |x| = x.
Axiom. If x is negative then |x| = -x.
Axiom. x is 0 iff |x| = 0.
Proposition. Let x be a real number. |x| >= 0.
Proposition. Let x be a real number. |-x| = |x|.
Proposition MultAbs. Let x,y be real numbers. |x*y| = |x|*|y|.
Proof.
  Case x is positive.
    Case y is positive. Then x*y is positive.
      |x*y| = x*y = |x|*|y|.
    end.
    Case y is negative. Then x*y is negative.
      |x*y| = -(x*y) = x*(-y) = |x|*|y|.
    end.
  end.
  Case x is negative.
    Case y is negative. Then x*y is positive.
      |x*y| = x*y = (-x)*(-y) = |x|*|y|.
    end.
    Case y is positive. Then x*y is negative.
      |x*y| = -(x*y) = (-x)*y = |x|*|y|.
    end.
  end.
qed.


Signature. dist(x,y) is a real number.
Axiom DistanceDef. dist(x,y) = |x - y|.
Proposition TriIneqAbs. Let x,y be real numbers. |x+y| <= |x| + |y|.
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

Signature. sqrt(x) is a real number.
Axiom. sqrt(x)*sqrt(x) = x.


### Sequences

Definition Seq.
    A sequence f is a map such that every element of Dom(f) is a natural number and every
    natural number is an element of Dom(f) and for every n f(n) is a real number.
Theorem. Let f be a sequence. Dom(f) = NN.
Proof. 
    Let us show that Dom(f) is a subset of NN. Trivial.
    Let us show that NN is a subset of Dom(f). Trivial.
end.

Axiom SequenceEq.
    Let a, b be sequences. a = b iff (for every n a(n) = b(n)).

### Convergence

Definition Convergence.
    Let a be a sequence. Let x be a real number. a converges to x iff for every positive real
    number eps there exists N such that for every n such that N < n dist(a(n),x) < eps.

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

    Define b(k) = |a(k)| for k in NN. b is a sequence.
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
    for n in NN.
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

    Take N1 such that for every n such that N1 < n dist(a(n),x) < halfeps.
    Take N2 such that for every n such that N2 < n dist(b(n),y) < halfeps.
    Take N such that N = max(N1,N2).
    Then N1 <= N and N2 <= N.

    Let us show that for every n such that N < n dist((a ++ b)(n),(x+y)) < eps.
        Let n be a natural number such that N < n.
        We have dist(a(n),x) < halfeps.
        We have dist(b(n),y) < halfeps.

        |(a(n) + b(n)) - (x + y)| .= |(a(n) + b(n)) + ((-x) + (-y))| (by MinusDist)
                                     .= |((a(n) + b(n)) + (-x)) + (-y)| (by  1_12_A3)
                                     .= |(-x + (a(n) + b(n))) - y| (by 1_12_A2)
                                     .= |((-x + a(n)) + b(n)) - y| (by  1_12_A3)
                                     .= |((a(n) - x) + b(n)) - y| (by  1_12_A2)
                                     .= |(a(n) - x) + (b(n) - y)|  (by  1_12_A3).

        We have |(a(n) - x) + (b(n) - y)| <= |a(n) - x| + |b(n) - y|.
        Hence |(a(n) + b(n)) - (x + y)| <= dist(a(n),x) + dist(b(n),y).

        Hence dist(a(n),x) + dist(b(n),y) < halfeps +  dist(b(n),y) < halfeps + halfeps.
        Hence |(a(n) + b(n)) - (x + y)| <= dist(a(n),x) + dist(b(n),y) <  halfeps + halfeps.
        Hence |(a(n) + b(n)) - (x + y)| <  halfeps + halfeps = eps.
        Hence dist((a ++ b)(n),(x + y)) < eps.
    end.
qed.

Lemma ConstConv.
  Let c be a real number. Let cn be a sequence such that for every n cn(n)=c. Then cn converges to c.

Theorem SumConstConv.
  Let a be a sequence. Let x,c be real numbers. Assume a converges to x. Then c+'a converges to c+x.
Proof.
    Define cn(n) = c for n in NN. cn is a sequence.
    Let us show that c +' a = cn ++ a.
        Let us show that (c +' a)(n) = (cn ++ a)(n) for every natural number n.
            Let n be a natural number.
            (c +' a)(n) .= c + a(n)
                         .= cn(n) + a(n)
                         .= (cn ++ a)(n).
        end.
        Hence c +' a = cn ++ a.
    end.
    cn converges to c.
    Then c +' a converges to c + x.
qed.

 
Theorem ProdConstConv.
  Let a be a sequence. Let x,c be real numbers. Assume a converges to x. Then c*'a converges to c*x.
Proof.
    Case c=0.
        We have c*x=0.
        Let us show that for every natural number n (c*'a)(n)=0.
          Let n be a natural number.
            (c*'a)(n) .=c*a(n)
                       .=0*a(n)
                       .=0.
        Hence c*'a converges to c*x.
        end.
    end.
    Case c!=0.
      Let eps be a positive real number.
      Take a positive real number oneovereps such that oneovereps = 1/(|c|)*eps.
      Take N such that for every n such that N<n dist(a(n),x)<oneovereps.
      Let us show that for every n such that N<n dist(c*(a(n)), c*x)< eps.
        Let n be natural number. Assume N<n.
        |(c*a(n))-(c*x)|  .=|c*(a(n)-x)| (by Dist2)
                          .=|c|*|(a(n)-x)| (by MultAbs).
        |c|*dist(a(n),x)<|c|*oneovereps.
        Hence |(c*a(n))-(c*x)|<|c|*oneovereps.
        |c|*oneovereps  = |c|*(1/(|c|)*eps) = (|c|*1/(|c|))*eps = 1*eps = eps.
        Therefore dist(c*(a(n)),c*x)<eps.
       end.
    end.
qed.


Lemma ConstMultSum.
  Let a,b be sequences. Let x,y be real numbers such that for every n b(n)=y*(a(n)+(-x)).
  Assume a converges to x. Then b converges to 0.
Proof.
    Define sum(k) = (-x) + a(k) for k in NN.
    sum is a sequence.
    Let us show that sum converges to 0.
        We have sum = (-x) +' a.
        Hence sum converges to (-x) + x.
        (-x) + x = 0.
    qed.
    Let us show that for every n b(n) = y * sum(n).
        Let n be a natural number.
        b(n) = y * (a(n) + (-x)) = y * ((-x) + a(n)) = y * sum(n).
    qed.
    Hence b = y *' sum.
    Hence b converges to 0.
qed.



Theorem ProdConv.
  Let a,b be sequences. Let x,y be real numbers. Assume a converges to x and b converges to y.
  Then a**b converges to x*y.
Proof.
    (1) Define s1(k) = (a(k) - x) * (b(k) - y) for k in NN.
    Let us show that s1 converges to 0.
        Let eps be a positive real number.
        Take a positive real number rooteps such that rooteps = sqrt(eps).
        Take N1 such that for every n such that N1 < n dist(a(n),x) < rooteps.
        Take N2 such that for every n such that N2 < n dist(b(n),y) < rooteps.
        Take N such that N = max(N1,N2).
        Let us show that for every n such that N < n dist(s1(n),0) < eps.
            Let n be a natural number such that N < n.
            dist(a(n),x) < rooteps and dist(b(n),y) < rooteps.
            dist(a(n),x), dist(b(n),y) and rooteps are not negative.
            Then dist(a(n),x) * dist(b(n),y) < eps.
            Hence |a(n) - x| * |b(n) - y| < eps.
            Hence |(a(n) - x) * (b(n) - y)| < eps.
            Hence |((a(n) - x) * (b(n) - y)) - 0| < eps.
       qed.
    qed.
    (2) Define s2(k) = (x * (b(k) + (-y))) + (y * (a(k) + (-x))) for k in NN.
    Let us show that s2 converges to 0.
        (3) Define s2a(k) = y * (a(k) + (-x)) for k in NN.
        (4) Define s2b(k) = x * (b(k) + (-y)) for k in NN.
        s2a, s2b are sequences.
        Define sum1(k) = a(k) + (-x) for k in NN.
        Define sum2(k) = b(k) + (-y) for k in NN.
        sum1, sum2 are sequences.
        sum1 = (-x) +' a and sum2 = (-y) +' b.
        sum1, sum2 converge to 0.
        We have s2a = y *' sum1 and s2b = x *' sum2.
        s2a, s2b converge to 0. 
        Let us show that for every n s2(n) = s2b(n) + s2a(n).
        Proof. Let n be a natural number.
            s2(n) .= (x * (b(n) + (-y))) + (y * (a(n) + (-x))) (by 2)
                  .= s2b(n) + s2a(n) (by 3, 4).
        qed.
        Hence s2 converges to 0.
    qed.
    (5) Define s3(k) = (a(k) * b(k)) - (x * y) for k in NN.
    Let us show that s3 converges to 0.
    proof.
        Let us show that for every n s3(n) = s1(n) + s2(n).
        Proof. Let n be a natural number.
            s3(n) .= (a(n) * b(n)) - (x * y) (by 5)
                  .= ((a(n) - x) * (b(n) - y)) + ((x * (b(n) - y)) + (y * (a(n) - x))) (by Identity1)
                  .= s1(n) + s2(n) (by 1, 2).
        qed.
        Hence s3 = s1 +' s2.
        Therefore the thesis.
    qed. 
    Let eps be a positive real number.
    Take N such that for every n such that N < n dist(s3(n),0) < eps.
    Let us show that for every n such that N < n dist(a(n) * b(n),x * y) < eps.
    Proof.
        Let n be a natural number such that N < n.
        dist(s3(n),0) .= dist((a(n) * b(n)) - (x * y),0) (by 5)
                      .= |((a(n) * b(n)) - (x * y)) - 0|
                      .= |(a(n) * b(n)) - (x * y)|
                      .= dist(a(n) * b(n),x * y).
    qed.
qed.



Theorem DivConv.
  Let a be a sequence. Let x be a real number such that x !=0. Assume a converges to x.
  Assume for every n a(n)!=0. Then div(a) converges to 1/x.
Proof.
    Let eps be a positive real number.
    |x| != 0.
    
    #could jus write take m such that. Then no yellow error.
                                                       
    Take m such that for every n such that m < n dist(a(n),x) < 1/2 * |x|.
    Let us show that for every n such that m < n 1/2 * |x| < |a(n)|.
        Let n be a natural number such that m < n.
        a(n), |a(n)|, -|a(n)|, |x| - |a(n)|, x - a(n), |x - a(n)|, a(n) - x, |a(n) - x|, |x| + (-|a(n)|), (|x| + (-|a(n)|)) + (-|x|) are real numbers.
        Let us show that |x| - |a(n)| < 1/2 * |x|.
            |x| - |a(n)| <= |x - a(n)|.
            |x - a(n)| = |-(x - a(n))| = |a(n) - x|.
            |a(n) - x| < 1/2 * |x|.
            Hence the thesis.
        qed.

        Let us show that -|a(n)| < (-1/2) * |x|.
            (|x| - |a(n)|) + (-|x|) < (1/2 * |x|) + (-|x|). 
            (|x| - |a(n)|) + (-|x|) = -|a(n)|.

            -|a(n)| < (1/2 * |x|) + (-|x|).
            (1/2 * |x|) + (-|x|) = (1/2 * |x|) + ((1/2*(-|x|)) + (1/2*(-|x|))) = (-1/2) * |x|.
        qed.

        Therefore |a(n)| > |x| * 1/2.
    qed.
   
    Take N1 such that for every n such that N1 < n dist(a(n),x) < (1/2 * eps) * (|x| * |x|). 
    Take N2 such that N2 = max(N1,m).
    Let us show that for every n such that N2 < n dist(1/a(n),1/x) < eps.
        Let n be a natural number such that N2 < n.
        Then we have N1 < n and m < n.
        Let us show that dist(1/a(n),1/x) < ((eps * (|x| * |x|)) * (1/2 * |1/x|)) * (1 * (1/|a(n)|)).
            dist(1/a(n),1/x) .= |1/a(n) - 1/x|
                              .= |(1*1/a(n)) - (1*1/x)| (by 1_12_M4)
                              .= |((x*1/x) * 1/a(n)) - ((a(n)*1/a(n)) * 1/x)| (by 1_12_M5)
                              .= |(x*(1/x * 1/a(n))) - (a(n)*(1/a(n) * 1/x))| (by 1_12_M3)
                              .= |(x*(1/x * 1/a(n))) - (a(n)*(1/x * 1/a(n)))| (by 1_12_M2)
                              .= |(x-a(n))*(1/x * 1/a(n))| (by Dist3)
                              .= |x-a(n)|*|1/x * 1/a(n)| (by MultAbs).
            |1/x * 1/a(n)| is positive.
            |x - a(n)| = dist(a(n),x).
            |x-a(n)|*|1/x * 1/a(n)|  < ((1/2 * eps) * (|x| * |x|)) * |1/x * 1/a(n)|.
        qed.

        (eps * (|x| * |x|)) * (1/2 * |1/x|), 1 * (1/|a(n)|), 2 * (1/|x|), dist(1/a(n),1/x),
        ((eps * (|x| * |x|)) * (1/2 * |1/x|)) * (1 * (1/|a(n)|)), ((eps * (|x| * |x|)) * (1/2 * |1/x|)) * (2 * (1/|x|)) are real numbers.
    end.
end.



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


###Problem


Lemma SubSeqLeq.
  Let a be a sequence. Let i be an index sequence. Then for every n n<=i(n).
Proof.
    Let us show by induction that n <= i(n) for every n.
        Let n be a natural number.
        Case n=0.
            Let us show that 0<= i(0).
              i(0) is a natural number.
              Therefore i(0)>= 0. 
            end.
        end.
        Case n != 0.
            Take m such that n=m+1.
            Hence m<n.
            Therefore  m<=i(m).
            Hence m+1 <= i(m)+1.
            Then i(m)<i(m+1). 
            Hence i(m)+1<= i(m+1).
            Then m+1 <= i(m+1).
            Hence n <= i(n).
        end.
    end.
qed.




Lemma LimitSubSeq.
  Let a be a sequence. Let x be a real number.
  a converges to x if and only if for every index sequence i Subseq(a,i) converges to x.
Proof. 
     Let us show that if a converges to x then for every index sequence i Subseq(a, i) converges to x.
          Assume a  converges to x.
          Let i be an index sequence. Let eps be a 
          positive real number. Take N such that for every n such that N<n dist(a(n),x)<eps.
          Let us show that for every n such that N<n dist(Subseq(a,i)(n),x)<eps.
              Let n be a natural number such that N<n.
              Then n<=i(n).
              Hence N< i(n).
              Hence dist(Subseq(a,i)(n),x)=dist(a(i(n)),x)<eps.
          qed.
      qed.

      Let us show that if for every index sequence i Subseq(a, i) converges to x
      then a converges to x.
            Assume for every index sequence i Subseq(a, i) converges to x.
            Define i(n) = n for n in NN.
            i is an index sequence.
            Subseq(a, i) converges to x.
            For every n a(n) = Subseq(a, i)(n).
            Hence a = Subseq(a, i).
            Hence a converges to x.
      qed.
qed.



Axiom BolzanoWeierstrass.
  Let a be a bounded sequence. Then a has some convergent subsequence.


### Cauchy Sequences

Definition Cauchy.
  A cauchy sequence is a sequence a such that for every positive real number eps there exists N such
  that for every n,m such that (N<n and N<m) dist(a(n),a(m))<eps.

Lemma CauchyBounded.
  Let a be a cauchy sequence. Then a is bounded.
Proof.
    Take N such that for every n,m such that (N < n and N < m) dist(a(n),a(m)) < 1.
    Hence for every n such that N < n dist(a(n),a(N + 1)) < 1.

    Define b(k) = |a(k)| for k in NN.

    Take a real number K such that K = max(1 + |a(N + 1)|, maxN(b,N)).

    Let us show that a is bounded by K.
        Let us show that for every n |a(n)| <= K.
            Let n be a natural number.
            Case n <= N.
                We have |a(n)| = b(n) <= maxN(b,N) (by MaxN).
                We have maxN(b,N) <= K.
                Therefore |a(n)| <= K.
            end.
            Case n > N.
                We have dist(a(n),a(N + 1)) < 1.
                We have 1 + |a(N + 1)| <= K.

                |a(n)| .= |a(n) + 0|
                          .= |a(n) + (a(N + 1) - a(N + 1))| (by 1_12_A5)
                          .= |a(n) + ((-a(N + 1)) + a(N + 1))| (by 1_12_A2)
                          .= |(a(n) - a(N + 1)) + a(N + 1)| (by 1_12_A3).
                          
                a(n) - a(N + 1) and a(N + 1) are real numbers.
                We have |(a(n) - a(N + 1)) + a(N + 1)| <= |a(n) - a(N + 1)| + |a(N + 1)| (by TriIneqAbs).
                Hence |a(n)| <= |a(n) - a(N + 1)| + |a(N + 1)|.
                Hence |a(n)| <= dist(a(n),a(N + 1)) + |a(N + 1)|.

                We have dist(a(n),a(N + 1)) + |a(N + 1)| < 1 + |a(N + 1)|.
                Hence |a(n)| <= 1 + |a(N + 1)| (by Trans1).
                Therefore |a(n)| <= K.
            end.
        end.
        Hence a is bounded by K (by BoundedBy).
    end.
qed.


Lemma CauchyConvSubSeq.
  Let a be a cauchy sequence such that a has some convergent subsequence.
  Then a converges.
Proof.
    Take a index sequence i such that Subseq(a,i) converges.
    Take a real number x such that Subseq(a,i) converges to x.

    Let us show that a converges to x.
        Let eps be a positive real number.
        Take a positive real number halfeps such that halfeps = 1/2 * eps.

        Take N1 such that for every n,m such that (N1 < n and N1 < m) dist(a(n),a(m)) < halfeps.
        Take N2 such that for every n such that N2 < n dist(Subseq(a,i)(n),x) < halfeps (by Convergence).
        Take N such that N = max(N1,N2).
        Then N1 <= N and N2 <= N.

        Let us show that for every n such that N < n dist(a(n),x) < eps.
            Let n be a natural number such that N < n. Hence N1 < n and N2 < n.
            We have n <= i(n) (by SubSeqLeq). Hence N1 < i(n).
            a(n), a(i(n)), dist(a(n),a(i(n))), dist(a(n),x), a(n) - a(i(n)), a(i(n)) - x, dist(a(n),a(i(n))) + dist(a(i(n)),x) are real numbers.

            We have Subseq(a,i)(n) = a(i(n)).
            We have dist(a(n),a(i(n))) < halfeps.
            We have dist(a(i(n)),x) < halfeps.

            dist(a(n),x) .= |a(n) - x|
                         .= |(a(n) + 0) - x|
                         .= |(a(n) + (a(i(n)) - a(i(n)))) - x| (by 1_12_A5)
                         .= |(a(n) + ((-a(i(n))) + a(i(n)))) - x| (by 1_12_A2)
                         .= |((a(n) - a(i(n))) + a(i(n))) - x| (by 1_12_A3)
                         .= |(a(n) - a(i(n))) + (a(i(n)) - x)| (by 1_12_A3).

            We have |(a(n) - a(i(n))) + (a(i(n)) - x)| <= |a(n) - a(i(n))| + |a(i(n)) - x| (by  TriIneqAbs).
            Hence dist(a(n),x) <= |a(n) - a(i(n))| + |a(i(n)) - x|.
            Hence dist(a(n),x) <= dist(a(n),a(i(n))) + dist(a(i(n)),x) (by DistanceDef).

            We have dist(a(n),a(i(n))) + dist(a(i(n)),x) < halfeps + halfeps (by  AddInvariance).
            Hence dist(a(n),x) < halfeps + halfeps (by Trans1).
            Hence dist(a(n),x) < eps.
        end.
    end.
qed.


Theorem RComplete.
  Let a be a sequence. a is cauchy sequence iff a converges.
Proof.
    Let us show that if a is a cauchy sequence then a converges.
        Assume a is a cauchy sequence.
        Then a is bounded (by CauchyBounded).
        Therefore a has some convergent subsequence (by BolzanoWeierstrass).
        Hence a converges (by CauchyConvSubSeq).
    end.

    Assume a converges.
    Take a real number x such that a converges to x.
    Let us show that a is a cauchy sequence.
        Let eps be a positive real number.
        
        Take a positive real number halfeps such that halfeps = 1/2 * eps.
        Take N such that for every n such that N < n dist(a(n),x) < halfeps.

        Let us show that for every n,m such that (N < n and N < m) dist(a(n),a(m)) < eps.
            Let n,m be natural numbers such that N < n and N < m.
            We have dist(a(n),x) < halfeps.
            We have dist(a(m),x) < halfeps.

            We have dist(a(n),a(m)) <= dist(a(n),x) + dist(x,a(m)).
            Hence dist(a(n),a(m)) <= dist(a(n),x) + dist(a(m),x).
            We have dist(a(n),x) + dist(a(m),x) < halfeps + halfeps (by AddInvariance).
            Hence dist(a(n),a(m)) < halfeps + halfeps (by Trans1).
            Hence dist(a(n),a(m)) < eps.
       end.
    end.
qed.


### Monotonic sequences

Definition MonInc.
  Let a be a sequence. a is monotonically increasing iff (for every n,m such that n<=m a(n)<=a(m)).

Definition MonDec.
  Let a be a sequence. a is monotonically decreasing iff (for every n,m such that n<=m a(n)>=a(m)).

Definition Mon. 
  Let a be a sequence. a is monotonic iff a is monotonically increasing
  or a is monotonically decreasing.

###Changed from upper bound to ubber bound

Definition UpperBoundSeq.
  Let a be a bounded sequence. Let K be a real number. K is ubber bound of a iff (for every n a(n)<=K).


Definition LeastUpperBoundSeq.
  Let a be a bounded sequence. LeastUpper(a) is a real number K such that (K is ubber bound of a)
  and (we have K<=L for every real number L such that L is ubber bound of a).


Definition LowerBoundSeq.
  Let a be a bounded sequence. Let K be a real number. K is lower bound of a iff (for every n a(n)>=K).

Definition GreatestLowerBoundSeq.
  Let a be a bounded sequence. GreatestLower(a) is a real number K such that (K is a lower bound of a)
  and (for every real number L such that L is a lower bound of a K>=L).


Lemma MonIncCon. 
  Let a be a monotonically increasing bounded sequence. Then a converges.
Proof.
    For every n a(n) <= LeastUpper(a) (by UpperBoundSeq, LeastUpperBoundSeq).
    Let us show that for every positive real number eps there exists N such that (LeastUpper(a) - eps) < a(N).
        Assume the contrary.
        Take a positive real number eps such that for every N not((LeastUpper(a) - eps) < a(N)).

        Let us show that for every n a(n) <= (LeastUpper(a) - eps).
            Let n be a natural number.
            We have not((LeastUpper(a) - eps) < a(n)).
            Therefore (LeastUpper(a) - eps) >= a(n).
            Hence a(n) <= (LeastUpper(a) - eps).
        end.
        Hence (LeastUpper(a) - eps) is upper bound of a.

        LeastUpper(a) - (LeastUpper(a) - eps) .= LeastUpper(a) + (-LeastUpper(a) + eps)
                                              .= (LeastUpper(a) - LeastUpper(a)) + eps (by 1_12_A3)
                                              .= 0 + eps (by 1_12_A5)
                                              .= eps + 0 (by 1_12_A2)
                                              .= eps.

        Hence (LeastUpper(a) - eps) < LeastUpper(a).
        Hence not((LeastUpper(a) - eps) >= LeastUpper(a)).
        Contradiction.
    end.

    Let us show that a converges to LeastUpper(a).
        Let eps be a positive real number.
        Take N such that (LeastUpper(a) - eps) < a(N).

        Let us show that for every n such that N < n dist(a(n),LeastUpper(a)) < eps.
            Let n be a natural number such that N < n.
            Hence a(N) <= a(n) (by MonInc).
            We have a(n) <= LeastUpper(a).
            Hence dist(a(n),LeastUpper(a)) = |LeastUpper(a) - a(n)| = LeastUpper(a) - a(n).

            We have (LeastUpper(a) - eps) + eps < a(N) + eps.
            We have ((LeastUpper(a) - eps) + eps) - a(N) < (a(N) + eps) - a(N).

            ((LeastUpper(a) - eps) + eps) - a(N) .= (LeastUpper(a) + (-eps + eps)) - a(N) (by 1_12_A3)
                                                 .= (LeastUpper(a) + (eps - eps)) - a(N) (by 1_12_A2)
                                                 .= (LeastUpper(a) + 0) - a(N) (by 1_12_A5)
                                                 .= LeastUpper(a) - a(N).

            (a(N) + eps) - a(N) .= (eps + a(N)) - a(N) (by 1_12_A2)
                                .= eps + (a(N) - a(N)) (by 1_12_A3)
                                .= eps + 0 (by 1_12_A5)
                                .= eps.

            Hence LeastUpper(a) - a(N) < eps.
            
            We have LeastUpper(a) - a(n) <= LeastUpper(a) - a(N).
            Hence dist(a(n),LeastUpper(a)) < eps.
        end.
    end.
qed.


Theorem MonCon.
  Let a be a monotonic sequence. a converges iff a is bounded.
Proof.
    We have (If a converges then a is bounded) (by ConvergentImpBounded).

    Assume a is bounded.
    Case a is monotonically increasing.
        Then a converges (by MonIncCon). 
    end.
    Case a is monotonically decreasing.
        Let us show that (-1) *' a is monotonically increasing.
            Let n,m be natural numbers such that n <= m.
            Then a(n) >= a(m) (by MonDec).
            Then -a(n) <= -a(m).
            
            ((-1) *' a)(n) .= (-1) * a(n)
                            .= -a(n).
            ((-1) *' a)(m) .= (-1) * a(m)
                            .= -a(m).

            Hence ((-1) *' a)(n) <= ((-1) *' a)(m).
        end.

        Let us show that (-1) *' a is bounded.
            Take a real number K such that for every n |a(n)| <= K (by BoundedSequence).

            Let us show that for every n |((-1) *' a)(n)| <= K.
                Let n be a natural number.
                |((-1) *' a)(n)| .= |(-1) * a(n)| (by SequenceConstProd)
                                     .= |-a(n)|
                                     .= |a(n)|.
                Hence |((-1) *' a)(n)| <= K.
            end.

            Hence (-1) *' a is bounded by K (by BoundedBy).
        end.

        Hence (-1) *' a converges (by MonIncCon).
        Take a real number x such that (-1) *' a converges to x.

        Let us show that (-1) *' ((-1) *' a) = a.
            Let us show that for every natural number n ((-1) *' ((-1) *' a))(n) = a(n).
                Let n be a natural number.
                ((-1) *' ((-1) *' a))(n) .= (-1) * ((-1) *' a)(n) (by SequenceConstProd)
                                           .= (-1) * ((-1) * a(n)) (by SequenceConstProd)
                                           .= -(-a(n))
                                           .= a(n).
            end.
            Hence (-1) *' ((-1) *' a) = a (by SequenceEq).
        end.

        Then (-1) *' ((-1) *' a) converges to (-1) * x (by ProdConstConv).
        Hence a converges (by Conv).
    end.
qed.



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
