
# Proof structure

* Absolute value on Q is determined by its values on the positive integers TODO

* Formalize the statement: We will prove
(a) |n| = n^t for all n in Nat (definition: Fabrizio & Sylvain DONE)
(b) n = |n|^t_p for some prime p and all n in Nat (definition: Francesco & Nirvana DONE).

* By cases, according to |n| > 1 or |n| <= 1

Case 1. When |n| > 1, we show (a) (Formalize the statement: Amos & Laura DONE)
- step 1: if |n|>1 for some n then |n|>1 for *all* n \geq 2 (by proving contrapositive)

- step 2: given m,n \geq 2 and |m|=m^s, |n|=n^t for s,t >0, prove t \leq s

- final step: finish the proof by symmetry (exchanging m,n and proving s \leq t)

Case 2. When |n| <= 1, we show (b) (Formalize the statement: Sam DONE)

- step 1: define p smallest n such that 0 < |p| < 1. 

- step 2: p is prime

- step 3: any integer m *not* divisible by p has |m| = 1

- step 4: |p|= (1/p)^t for some t >0. Then |x| = |x|_p^t

