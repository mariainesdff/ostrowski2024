# Ostrowski Theorem in Lean
# LFTCM 2024

## Team

- David Kurniadi Angdinata (UCL)
- Fabrizio Barroero (Roma Tre University)
- Laura Capuano (Roma Tre University)
- Nirvana Coppola (Université de Strasbourg)
- María Inés de Frutos Fernández (Universidad Autónoma de Madrid)
- Silvain Rideau-Kikuchi (CNRS ENS - PSL)
- Amos Turchet (Roma Tre University)
- Sam van Gool (Université Paris Cité)
- Francesco Veneziano (University of Genova)

## Motivation
- previous project (XenaProject 2022 led by María Inés) had an (almost) complete proof in Lean3 for `\Q`
- we wanted a proof in Lean 4 which allows generalization to Number Fields and Function Fields (future?)

## Mathematical History

* Ostrowski's original paper appeared in 1916
* Complete characterization of all absolute values in `\Q` 
* We follow Conrad's outline of the proof:
[https://kconrad.math.uconn.edu/blurbs/gradnumthy/ostrowskiQ.pdf]

## Mathematical Setting

* Absolute values are implemented in Lean as `MulRingNorm R`
* Equivalent absolute values are defined as
```
def equiv {R : Type*} [Ring R] (f : MulRingNorm R) (g : MulRingNorm R) :=
∃ c : ℝ, 0 < c ∧ (λ x : R => (f x) ^ c) = g
```
* An absolute value is characterized by its values on the naturals
```
lemma NormRat_eq_iff_eq_on_Nat : (∀ n : ℕ , f n = g n) ↔ f = g
```
* The proof is by cases:
```
theorem ringNorm_padic_or_real (f : MulRingNorm ℚ) (hf_nontriv : f ≠ 1) :
    (MulRingNorm.equiv f mulRingNorm_real) ∨
    ∃ (p : ℕ) (hp : Fact (Nat.Prime p)), MulRingNorm.equiv f (@mulRingNorm_padic p hp) := by
  by_cases bdd : ∀ n : ℕ, f n ≤ 1
  · right
    apply bdd_implies_equiv_padic bdd hf_nontriv
  · left
    apply notbdd_implies_equiv_real bdd
```

## Some hiccups
 
* For the Archimedean part we needed to work with integers in different bases (using `Nat.digits`) which meant handling lists and their interaction with `MulRingNorm`;

* We were not able to effectively use available tactics for handling formulas (i.e. `linarith`, `omega`, `gcongr`) in expressions involving several casts;


------------------