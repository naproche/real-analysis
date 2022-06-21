[read real-analysis/numbers.ftl]

[synonym sequence/-s]
[synonym converge/-s]

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
Proposition. Let x,y be real numbers. |x+y| =< |x| + |y|.
Proof.
Case x+y is positive. Then |x+y| = x+y =< |x| + |y|. end.
Case x+y is negative. 
  |x+y| = -(x+y) = (-x) + (-y) =< |-x| + |-y| = |x| + |y|.
end. qed.

Lemma Trinagle inequality. Let x,y,z be real numbers. Then
dist(x,y) =< dist(x,z) + dist(z,y).
Proof.
dist(x,y) = |x - y| = |(x-z) + (z-y)| =< |x-z| + |z-y| =  dist(x,z) + dist(z,y).
qed.

Lemma. Let x,y be real numbers. dist(x,y) = dist(y,x).
Proof. dist(x,y) = |x - y| = |-(x - y)| = |y - x| = dist(y,x). qed.

Signature. max(x,y) is a real number.
Axiom. If x >= y then max(x,y) = x.  
Axiom. If x < y then max(x,y) = y.


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
    Let a be a sequence. ranN(a,N) = {a(n) | n is a natural number such that n =< N}.

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
            Let us show that for every n such that n =< N a(n) != a(N + 1).
                Assume the contrary.
                Take n such that n =< N and a(n) = a(N + 1).
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
        We have dist(a(N + 1),a(N + 2)) =< dist(a(N + 1),x) + dist(x,a(N + 2)).
        We have dist(x,a(N + 2)) = dist(a(N + 2),x).
        Hence dist(a(N + 1),a(N + 2)) =< dist(a(N + 1),x) + dist(a(N + 2),x).

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
                Take n such that n =< 1 and a(n) = x.
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
                    We have 0 =< 1.
                    Hence x is an element of ranN(a,1).
                end.
                Case x = -1.
                    Then x = a(1).
                    We have 1 =< 1.
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

        For every n dist(x,y) =< dist(x,a(n)) + dist(a(n),y). 
        Take N3 such that N3 = max(N1,N2) + 1.
        Then N1 < N3 and N2 < N3.

        Hence dist(x,a(N3)) < halfeps and dist(a(N3),y) < halfeps.
        Hence dist(x,a(N3)) + dist(a(N3),y) <  dist(x,a(N3)) + halfeps < halfeps + halfeps.
        Hence dist(x,y) =< dist(x,a(N3)) + dist(a(N3),y) < halfeps + halfeps = (1/2 + 1/2)*eps = eps.
    end.
    Therefore x = y.
qed.