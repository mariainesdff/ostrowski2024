import Mathlib.Algebra.Group.WithOne.Defs
import Mathlib.Algebra.Order.CompleteField
import Mathlib.Algebra.Quotient
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.NumberTheory.NumberField.Embeddings
import Mathlib.NumberTheory.Ostrowski
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.Ideal.Norm
import Mathlib.Tactic.Rify
import Mathlib.Topology.Algebra.Valued.NormedValued
import Ostrowski2024.Rationals
import Ostrowski2024.WithZero

/-!
# Ostrowski's theorem for number fields

## References
* https://kconrad.math.uconn.edu/blurbs/gradnumthy/ostrowskiQ.pdf
* https://kconrad.math.uconn.edu/blurbs/gradnumthy/ostrowskinumbfield.pdf

## Tags
ring_norm, ostrowski
-/

/-!
Throughout this file, `f` is an arbitrary absolute value.
-/

-- some proposals of homorpshism between algebraic structures with absolute values

structure NormHom {R S : Type*} [NonAssocRing R] (f : MulRingNorm R) [NonAssocRing S] (g : MulRingNorm S) where
  toFun : R → S
  map_norm : g ∘ toFun = f

structure MulRingNormHom {R S : Type*} [NonAssocRing R] (f : MulRingNorm R) [NonAssocRing S] (g : MulRingNorm S) extends
  R →+* S, NormHom f g

structure MulRingNormIso {R S : Type*} [NonAssocRing R] (f : MulRingNorm R) [NonAssocRing S] (g : MulRingNorm S) extends
  R ≃+* S, NormHom f g

structure NormHomEquiv {R S : Type*} [NonAssocRing R] (f : MulRingNorm R) [NonAssocRing S] (g : MulRingNorm S) where
  toFun : R → S
  map_norm : ∃ (c : ℝ), 0 < c ∧ (g ∘ toFun) ^ c = f

structure MulRingNormHomEquiv {R S : Type*} [NonAssocRing R] (f : MulRingNorm R) [NonAssocRing S] (g : MulRingNorm S) extends
  R →+* S, NormHomEquiv f g

structure MulRingNormIsoEquiv {R S : Type*} [NonAssocRing R] (f : MulRingNorm R) [NonAssocRing S] (g : MulRingNorm S) extends
  R ≃+* S, NormHomEquiv f g
section completion

variable {R : Type*} [Ring R] (f : MulRingNorm R)

/- link between MulRingNorm and absolute values -/
instance MulRingNorm_is_absolute_value : IsAbsoluteValue f := {
  abv_nonneg' := apply_nonneg f
  abv_eq_zero' := by simp only [map_eq_zero_iff_eq_zero, implies_true]
  abv_add' := map_add_le_add f
  abv_mul' := MulHomClass.map_mul f
}

def MulRingNorm_from_abs [Nontrivial R] (abv : AbsoluteValue R ℝ) : MulRingNorm R where
  toFun := abv
  map_zero' := map_zero abv
  add_le' := AbsoluteValue.add_le abv
  neg' := by simp only [map_neg_eq_map, implies_true]
  map_one' := map_one abv
  map_mul' := by simp only [map_mul, implies_true]
  eq_zero_of_map_eq_zero' := by simp only [map_eq_zero_iff_eq_zero, imp_self, implies_true]

/- Completion -/
noncomputable def Completion : Type u_1 := CauSeq.Completion.Cauchy f

noncomputable instance ring_completion : Ring (Completion f) := CauSeq.Completion.Cauchy.ring

noncomputable instance field_completion [Field K] (f : MulRingNorm K) : Field (Completion f) := CauSeq.Completion.Cauchy.field


theorem foo (x y : R) :  f x - f y ≤ f (x - y) := by
  simp only [tsub_le_iff_right]
  apply le_trans _ (f.add_le' (x - y) y)
  simp only [sub_add_cancel, AddGroupSeminorm.toFun_eq_coe, MulRingSeminorm.toFun_eq_coe]
  exact Preorder.le_refl (f x)

/- Extend a MulRingNorm to the completion -/
noncomputable def MulRingNorm_Completion : MulRingNorm (Completion f) where
  toFun := by
    apply Quotient.lift
    swap
    intro s
    let s1 := s.val
    --let v : ℕ → ℝ := f ∘ s1
    have hcauchy : IsCauSeq abs (f ∘ s1) := by
      intro e he
      rcases s.2 (e / 2) (by linarith [he]) with ⟨i, h⟩
      use i
      intro j hj
      rw [abs_lt]
      specialize h j hj
      constructor
      · simp only [Function.comp_apply, neg_lt_sub_iff_lt_add]
        --have :
        sorry
      · --apply lt_trans _ h

        sorry
    exact CauSeq.lim ⟨f ∘ s1 , hcauchy⟩
    intro a b hab
    simp only
    refine CauSeq.lim_eq_lim_of_equiv ?_

    sorry
  map_zero' := by
    simp only

    sorry
  add_le' := by sorry
  neg' := by sorry
  map_one' := by sorry
  map_mul' := by sorry
  eq_zero_of_map_eq_zero' := by sorry

/- A completion is complete -/
noncomputable instance complete_completion : CauSeq.IsComplete (Completion f) (MulRingNorm_Completion f) := by sorry

def MulRingNorm_standard_R : MulRingNorm ℝ where
  toFun := fun x ↦ |x|
  map_zero' := abs_zero
  add_le' := abs_add_le
  neg' := abs_neg
  map_one' := abs_one
  map_mul' := abs_mul
  eq_zero_of_map_eq_zero' := by simp only [abs_eq_zero, imp_self, implies_true]

--CauSeq.Completion.ofRatRingHom

noncomputable def iso_to_R {f : MulRingNorm ℚ} (notbdd : ¬ ∀ n : ℕ, f n ≤ 1) :
    MulRingNormIsoEquiv (MulRingNorm_Completion f) MulRingNorm_standard_R := {
  toFun := by
    apply Quotient.lift
    swap
    intro s
    let s1 := s.val
    have : IsCauSeq abs s1 := by
      intro ε hε
      rcases (s.2 ε (mod_cast hε)) with ⟨i, hi⟩
      use i
      sorry
    let r : CauSeq ℚ abs := ⟨s1, this⟩
    exact Real.mk r
    simp only
    intro a b hab
    sorry
  invFun := by sorry
  left_inv := by sorry
  right_inv := by sorry
  map_mul' := by sorry
  map_add' := by sorry
  map_norm := by sorry
}

end completion

variable {K : Type*} [Field K] (f g : MulRingNorm K)

section restriction

variable (K' : Type*) [Field K'] [Algebra K' K]

def mulRingNorm_restriction : MulRingNorm K' :=
{ toFun     := fun x : K' ↦ f (x • (1 : K))
  map_zero' := by simp only [zero_smul, map_zero]
  add_le'   := by intro r s; simp only; rw [add_smul]; exact map_add_le_add f (r • 1) (s • 1)
  neg'      := by simp only [neg_smul, map_neg_eq_map, implies_true]
  eq_zero_of_map_eq_zero' := by simp only [map_eq_zero, smul_eq_zero, one_ne_zero, or_false,
    imp_self, implies_true]
  map_one' := by simp only [one_smul, map_one]
  map_mul' := by
    intro x y
    simp only
    nth_rw 1 [← one_mul (1 : K)]
    rw [← smul_mul_smul]
    exact MulHomClass.map_mul f (x • 1) (y • 1)
}

lemma restr_def (x : K') : (mulRingNorm_restriction f K') x = f (x • (1 : K)) := rfl

/- lemma nontriv_restriction : f ≠ 1 ↔ mulRingNorm_restriction f K' ≠ 1 := by
  sorry -/

end restriction


open NumberField

variable {K : Type*} [Field K] [nf : NumberField K] [DecidableEq K] (f : MulRingNorm K)
  (hf_nontriv : f ≠ 1)

theorem non_arch_iff_bdd : (∀ n : ℕ, f n ≤ 1) ↔  ∀ x y : K, f (x + y) ≤ max (f x) (f y) := by
--https://zb260.user.srcf.net/notes/III/local.pdf Lemma 3.5
--this is also done in somebody's project, see Zulip
  constructor
  · sorry
  · sorry

lemma bdd_restr_Q : (∀ n : ℕ, f n ≤ 1) ↔ (∀ n : ℕ, (mulRingNorm_restriction f ℚ) n ≤ 1) := by
  refine forall_congr' ?h
  intro n
  simp only [restr_def, Rat.smul_one_eq_cast, Rat.cast_natCast]

section Archimedean

variable (notbdd : ¬ ∀ n : ℕ, f n ≤ 1)

-- Archimedean mulRingNorm associated to a complex embedding
noncomputable def mulRingNorm_arch (φ : K →+* ℂ) : MulRingNorm K :=
{ toFun     := fun x : K ↦ ‖φ x‖
  map_zero' := by simp only [map_zero, norm_zero]
  add_le'   := by intro r s; simp only [map_add, Complex.norm_eq_abs]
                  exact AbsoluteValue.add_le Complex.abs (φ r) (φ s)
  neg'      := by simp only [map_neg, norm_neg, Complex.norm_eq_abs, implies_true]
  eq_zero_of_map_eq_zero' := by simp only [Complex.norm_eq_abs, map_eq_zero, imp_self, implies_true]
  map_one' := by simp only [map_one, norm_one]
  map_mul' := by simp only [map_mul, norm_mul, Complex.norm_eq_abs, implies_true]
}

include notbdd in
/--The restriction of an archimedean MulRingNorm to the rational is the standard absolute value -/
lemma restr_to_Q_real : MulRingNorm.equiv (mulRingNorm_restriction f ℚ) Rational.mulRingNorm_real := by
  apply Rational.mulRingNorm_equiv_standard_of_unbounded
  intro h
  rw [← bdd_restr_Q] at h
  exact notbdd h

include notbdd in
/-- Archimedean Ostrowski -/
theorem ostr_arch :
    ∃ φ : K →+* ℂ, (MulRingNorm.equiv f (mulRingNorm_arch φ) ∧
    ∀ ψ : K →+* ℂ, (MulRingNorm.equiv f (mulRingNorm_arch ψ)) →
    (ψ = φ ∨ NumberField.ComplexEmbedding.conjugate ψ = φ) ) := by
  -- pull ∃ c outside
  convert_to ∃ c : ℝ, 0 < c ∧ (∃ φ, (fun x => f x ^ c) = ⇑(mulRingNorm_arch φ) ∧ (∀ (ψ : K →+* ℂ), f.equiv (mulRingNorm_arch ψ) → ψ = φ ∨ ComplexEmbedding.conjugate ψ = φ))
  constructor
  · intro h
    rcases h with ⟨φ, h1, h2⟩
    rcases h1 with ⟨c, hc⟩
    use c
    refine ⟨hc.1, ?_⟩
    use φ
    exact And.symm (And.imp_left (fun a => h2) hc)
  · intro h
    rcases h with ⟨c , h1, h2⟩
    rcases h2 with ⟨φ, h3⟩
    use φ
    refine ⟨?_, h3.2⟩
    use c
    exact And.imp_left (fun a => h1) (id (And.symm h3))
  rcases restr_to_Q_real f notbdd with ⟨c, hc1, hc2⟩
  use c
  refine ⟨hc1, ?_⟩
  set K₀ := Completion f with hcomplK
  have hfK₀ : Field K₀ := CauSeq.Completion.Cauchy.field
  set Q₀ := Completion (mulRingNorm_restriction f ℚ) with hcomplQ
  have hfQ₀ : Field Q₀ := CauSeq.Completion.Cauchy.field
  rcases Field.exists_primitive_element ℚ K with ⟨γ, hγ⟩

  --  CauSeq.Completion.ofRat : The map from the original ring into the Cauchy completion.


  sorry

end Archimedean

section Nonarchimedean

section mulRingNorm_Padic

variable (P : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) -- P is a nonzero prime ideal of 𝓞 K

/-- P-adic valuation of a nonzero element of K  -/
noncomputable def val_P (x : K) (h_x_nezero : x ≠ 0) :=
    - Multiplicative.toAdd (WithZero.unzero ((Valuation.ne_zero_iff P.valuation).mpr h_x_nezero))

/-- A non zero prime ideal of 𝓞 K contains a unique prime number -/
lemma exist_prime_in_prime_ideal : ∃! (p : ℕ), ∃ (_ : Fact (p.Prime)), (↑p ∈ P.asIdeal) := by
  let r := Ideal.absNorm P.asIdeal
  set k := 𝓞 K ⧸ P.asIdeal
  have : Field k := Ideal.Quotient.field P.asIdeal
  have : Fintype k := Ideal.fintypeQuotientOfFreeOfNeBot P.asIdeal P.ne_bot
  rcases FiniteField.card' k with ⟨p, n, hp, hcard⟩
  have : r = p ^ (n : ℕ) := by
    rw [← hcard]
    simp only [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card, r, k]
  have hpmem : ↑p ∈ P.asIdeal := by
    apply Ideal.IsPrime.mem_of_pow_mem P.isPrime n
    norm_cast
    rw [← this]
    exact Ideal.absNorm_mem P.asIdeal
  use p
  constructor
  · simp only [exists_prop] --existence
    refine ⟨{ out := hp }, hpmem⟩
  · intro q hq --uniqueness
    rcases hq with ⟨hq1, hq2⟩
    by_contra! hpq
    rw [← Nat.coprime_primes hq1.out hp] at hpq
    apply Nat.Coprime.isCoprime at hpq
    rcases hpq with ⟨a, b, hid⟩
    have := Ideal.add_mem P.asIdeal (Ideal.mul_mem_left P.asIdeal a hq2) (Ideal.mul_mem_left P.asIdeal b hpmem)
    rw_mod_cast [hid] at this
    have hPprime := P.isPrime
    rw [Ideal.isPrime_iff] at hPprime
    apply hPprime.1
    rw [Ideal.eq_top_iff_one]
    exact_mod_cast this

/-- The unique prime number contained in P -/
noncomputable def prime_in_prime_ideal : ℕ := Exists.choose (exist_prime_in_prime_ideal P)

lemma prime_in_prime_ideal_is_prime : Fact ((prime_in_prime_ideal P).Prime) := (Exists.choose_spec (exist_prime_in_prime_ideal P)).1.1

lemma prime_in_prime_ideal_is_in_prime_ideal : (↑(prime_in_prime_ideal P) ∈ P.asIdeal) := (Exists.choose_spec (exist_prime_in_prime_ideal P)).1.2

lemma p_ne_zero (p : ℕ) (hp : Fact (p.Prime)) : (p : NNReal) ≠ 0 := by
  simp only [ne_eq, Nat.cast_eq_zero]
  exact NeZero.ne p

lemma one_lt_p (p : ℕ) (hp : Fact (p.Prime)) : 1 < (p : NNReal) := mod_cast Nat.Prime.one_lt (Fact.elim hp)

/--The P-adic absolute value -/
-- Now we have p ^ - v_p (x). Do we want to add the ramification index of P as a factor in the exponent?
noncomputable def mulRingNorm_Padic : MulRingNorm K :=
{ toFun     := fun x : K ↦ withZeroMultIntToNNReal (p_ne_zero (prime_in_prime_ideal P)
    (prime_in_prime_ideal_is_prime P)) (((IsDedekindDomain.HeightOneSpectrum.valuation P) x))
  map_zero' := by simp only [map_zero]; exact rfl
  add_le'   := by
    simp only
    let p := prime_in_prime_ideal P
    let hp := prime_in_prime_ideal_is_prime P
    intro x y
    norm_cast
    -- the triangular inequality is implied by the ultrametric one
    apply le_trans _ <| max_le_add_of_nonneg (by simp only [zero_le]) (by simp only [zero_le])
    have mono := StrictMono.monotone (withZeroMultIntToNNReal_strictMono (one_lt_p p hp))
    rw [← Monotone.map_max mono] --max goes inside withZeroMultIntToNNReal
    exact mono (Valuation.map_add P.valuation x y)
  neg'      := by simp only [Valuation.map_neg, implies_true]
  eq_zero_of_map_eq_zero' := by simp_all only [NNReal.coe_eq_zero, map_eq_zero, implies_true]
  map_one' := by simp only [map_one, NNReal.coe_eq_one]
  map_mul' := by simp only [map_mul, NNReal.coe_mul, implies_true]
}

--theorem connecting mulRingNorm_Padic and valP
theorem mulRingNorm_Padic_eq_p_pow_valP (x : K) (h_x_nezero : x ≠ 0) : (mulRingNorm_Padic P) x =
    (prime_in_prime_ideal P) ^ (- (val_P P x h_x_nezero)) := by
  have : (mulRingNorm_Padic P) x = (mulRingNorm_Padic P).toFun x := rfl
  rw [this]
  simp only [mulRingNorm_Padic]
  rw [withZeroMultIntToNNReal_neg_apply _ ((Valuation.ne_zero_iff P.valuation).mpr h_x_nezero)]
  simp only [NNReal.coe_zpow, NNReal.coe_natCast]
  have hprime := Fact.elim (prime_in_prime_ideal_is_prime P)
  refine (zpow_inj (mod_cast Nat.Prime.pos hprime) (mod_cast Nat.Prime.ne_one hprime)).mpr ?_
  exact Int.eq_neg_comm.mp rfl

--We have some examples ignore the next three things

def threeId : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ) where
  asIdeal := Ideal.span {3}
  isPrime := by
    refine (Ideal.span_singleton_prime ?hp).mpr ?_
    exact Ne.symm (OfNat.zero_ne_ofNat 3)

    sorry
  ne_bot := by
    refine (Submodule.ne_bot_iff (Ideal.span {3})).mpr ?_
    use 3
    constructor
    exact Ideal.mem_span_singleton_self 3
    exact Ne.symm (OfNat.zero_ne_ofNat 3)

example : IsDedekindDomain.HeightOneSpectrum.valuation (threeId) (2 : ℚ) = 1 := by
  have h1 : threeId.valuation (2 : ℚ) ≤ 1 := by
    --apply IsDedekindDomain.HeightOneSpectrum.valuation_le_one
    sorry
  have h2 : ¬ threeId.valuation (2 : ℚ) < 1 := by sorry
  simp only [not_lt] at h2
  apply eq_of_le_of_le
  exact h1
  exact h2

example : IsDedekindDomain.HeightOneSpectrum.valuation (threeId) (3 : ℚ) = Multiplicative.toAdd 1 := by
  --apply?
  sorry

-- end examples


--The next lemma is a general fact in algebraic number theory.
--This might be complicated, Conrad uses the class group but we might try with norms or minimal polynomials
lemma exists_num_denom_MulRingNorm_one (α : K) (h_nezero : α ≠ 0)
    (h_abs : mulRingNorm_Padic P α ≤ 1) : ∃ x y : 𝓞 K, α = x / y ∧ mulRingNorm_Padic P y = 1 := by
    sorry

end mulRingNorm_Padic

variable (nonarch : ∀ x y : K, f (x + y) ≤ max (f x) (f y)) (hf_nontriv : f ≠ 1)

include nonarch in
/-- ultrametric inequality with Finset.Sum  -/
lemma nonarch_sum_sup (α : Type*) (s : Finset α) (hnonempty : s.Nonempty) (l : α → K) : f (∑ i ∈ s, l i) ≤
  s.sup' hnonempty fun i => f (l i) := by
  let p : (a : Finset α) → Finset.Nonempty a → Prop := fun a hn => f (∑ i ∈ a, l i) ≤ a.sup' hn fun i => f (l i)
  convert_to p s hnonempty
  apply Finset.Nonempty.cons_induction
  simp [p]
  intro a s h hs hind
  simp [p]
  rw [← Finset.le_sup'_iff hs]
  --should be easy to finish
  sorry

open Polynomial minpoly

include nonarch in
/-- 𝓞 K is contained in the closed unit ball -/
lemma integers_closed_unit_ball (x : 𝓞 K) : f x ≤ 1 := by
  --rcases NumberField.RingOfIntegers.isIntegral x with ⟨P, hP1, hP2⟩
  let P := minpoly ℤ x
  have hminp : x ^ P.natDegree = ∑ i ∈ Finset.range P.natDegree, -((P.coeff i) * x ^ i) := by
    simp only [Finset.sum_neg_distrib, eq_neg_iff_add_eq_zero]
    let Q := Polynomial.X ^ P.natDegree + ∑ i ∈ Finset.range P.natDegree, Polynomial.C (P.coeff i) * Polynomial.X ^ i
    have heval : (Polynomial.aeval x) P = 0 := minpoly.aeval ℤ x
    have hPmonic : P.Monic := (minpoly.monic (NumberField.RingOfIntegers.isIntegral x))
    have hlcoeff1 : (P.coeff P.natDegree) = 1 := by
      simp only [coeff_natDegree]
      exact hPmonic
    have : P = Q := Polynomial.Monic.as_sum (minpoly.monic (NumberField.RingOfIntegers.isIntegral x))
    rw [← heval, Polynomial.aeval_eq_sum_range]
    simp only [zsmul_eq_mul]
    have : x ^ P.natDegree = (P.coeff P.natDegree) * x ^ P.natDegree := by
      rw [hlcoeff1]
      simp only [Int.cast_one, one_mul]
    rw [this]
    exact Eq.symm (Finset.sum_range_succ_comm (fun x_1 => ↑(P.coeff x_1) * x ^ x_1) P.natDegree)
  have hineq1 : ∀ i ∈ Finset.range P.natDegree, f (-(↑(P.coeff i) * x ^ i)) ≤ (f x) ^ i := by
    sorry
  by_contra! hc
  have hineq2 : ∀ i ∈ Finset.range P.natDegree, f (-(↑(P.coeff i) * x ^ i)) ≤ (f x) ^ (P.natDegree - 1) := by
    intro i hi
    specialize hineq1 i hi
    apply le_trans hineq1
    gcongr
    exact le_of_lt hc
    rw [Finset.mem_range] at hi
    exact Nat.le_sub_one_of_lt hi
  have h₀ : (x : K) ^ P.natDegree = ↑(x ^ P.natDegree) := rfl
  have hnezerodeg : P.natDegree ≠ 0 := by
    --minpoly.natDegree_pos
    sorry
  have hineq3 : (f x) ^ P.natDegree ≤ (f x) ^ (P.natDegree - 1) := by
    nth_rewrite 1 [← map_pow, h₀, hminp]
    apply Finset.sup'_le (Finset.nonempty_range_iff.mpr hnezerodeg) at hineq2
    apply le_trans _ hineq2
    push_cast
    simp only [map_intCast, Finset.sum_neg_distrib, map_neg_eq_map, map_pow]
    exact
      nonarch_sum_sup f nonarch ℕ (Finset.range P.natDegree)
        (Eq.refl (Finset.range P.natDegree) ▸ Finset.nonempty_range_iff.mpr hnezerodeg) fun i =>
        ↑(P.coeff i) * ↑x ^ i
  have : f x ≤ 1 := by
    by_contra! h
    apply not_lt_of_le at hineq3
    apply hineq3
    gcongr
    exact hc
    exact Nat.sub_one_lt hnezerodeg
  apply not_lt_of_le at this
  exact this hc

local notation3 "𝓟" => {a : (𝓞 K) | f a < 1}

include nonarch hf_nontriv in
/-- The open unit ball in 𝓞 K is a non-zero prime ideal of 𝓞 K. -/
lemma exists_ideal : ∃ P : IsDedekindDomain.HeightOneSpectrum (𝓞 K), 𝓟 = P.asIdeal.carrier := by
  use
  { asIdeal := {carrier   := 𝓟
                add_mem'  := by
                  simp only [Set.mem_setOf_eq, map_add]
                  exact fun ha hb => lt_of_le_of_lt (nonarch _ _) (max_lt ha hb)
                zero_mem' := by simp only [Set.mem_setOf_eq, map_zero, zero_lt_one]
                smul_mem' := by
                  simp only [Set.mem_setOf_eq, smul_eq_mul, map_mul]
                  exact fun c x hx => Right.mul_lt_one_of_le_of_lt_of_nonneg
                    (integers_closed_unit_ball f nonarch c) hx (apply_nonneg f ↑x)
                }
    isPrime := by
      rw [Ideal.isPrime_iff]
      constructor
      -- P is not 𝓞 K:
      · rw [Ideal.ne_top_iff_one]
        simp only [Submodule.mem_mk, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk,
          Set.mem_setOf_eq, map_one, lt_self_iff_false, not_false_eq_true]
      -- x * y ∈ P → x ∈ P ∨ y ∈ P:
      · simp only [Submodule.mem_mk, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk,
        Set.mem_setOf_eq, map_mul]
        intro x y hxy
        --easy
        sorry
    ne_bot  := by
      -- P ≠ 0
      --should not be hard
      rw [Submodule.ne_bot_iff]
      by_contra! h
      apply hf_nontriv
      simp only [Submodule.mem_mk, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk, Set.mem_setOf_eq] at h
      refine MulRingNorm.ext_iff.mpr ?_
      simp only [MulRingNorm.apply_one]
      intro x
      sorry
  }

include nonarch hf_nontriv in
theorem Ostr_nonarch : ∃! P : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
    MulRingNorm.equiv f (mulRingNorm_Padic P) := by
  rcases exists_ideal f hf_nontriv nonarch with ⟨P, hP⟩
  rcases IsDedekindDomain.HeightOneSpectrum.intValuation_exists_uniformizer P with ⟨π, hπ⟩ --uniformizer, this gives the constant c
  have hpi_nezero : π ≠ 0 := by
    by_contra! h
    rw [h] at hπ
    simp only [IsDedekindDomain.HeightOneSpectrum.intValuationDef_zero, Int.reduceNeg, ofAdd_neg,
      WithZero.coe_inv, zero_eq_inv, WithZero.zero_ne_coe] at hπ
  have hπ_val : P.intValuationDef π < 1 := by
    rw [hπ]
    exact WithZero.ofAdd_neg_one_lt_one
  have hπ_f_gt_zero : 0 < f π := by
    sorry
  have hπ_f_lt_one : f π < 1 := by
    sorry
  use P
  --extract the prime number p inside P
  let p' := prime_in_prime_ideal P
  have hp_prime_fact' : Fact (Nat.Prime p') := prime_in_prime_ideal_is_prime P
  have hp_prime' := hp_prime_fact'.elim
  have hPmem' : ↑p' ∈ P.asIdeal := prime_in_prime_ideal_is_in_prime_ideal P
  have hp_gt_one : 1 < p' := by exact Nat.Prime.one_lt hp_prime'
  rcases exist_prime_in_prime_ideal P with ⟨p, hp1, hp2⟩
  rcases hp1 with ⟨hp_prime_fact, hPmem⟩
  have hp_prime := hp_prime_fact.elim
  have h_f_p_lt_one : f p < 1 := by
    --not sure this is useful
    --use the fact that p is in P
    sorry
 /-  have hf_restr_nontriv : mulRingNorm_restriction f ℚ ≠ 1 := by
    simp
    rw [← Rat.MulRingNorm.eq_on_nat_iff_eq]
    simp only [MulRingNorm.apply_one, Nat.cast_eq_zero, not_forall]
    use p
    rw [@restr_def]
    simp only [Rat.smul_one_eq_cast, Rat.cast_natCast]
    have ha : ¬ p = 0 := by exact NeZero.ne p
    intro h
    simp only [ha, ↓reduceIte] at h
    linarith only [h_f_p_lt_one, h] -/
  -- extract c from rational case, wrong, useless?
 /-  have h_restr_bdd : ∀ (n : ℕ), mulRingNorm_restriction f ℚ n ≤ 1 := by
    simp only [restr_def, Rat.smul_one_eq_cast, Rat.cast_natCast]
    rw [← non_arch_iff_bdd] at nonarch
    exact fun n => nonarch n
  rcases Rat.MulRingNorm.mulRingNorm_equiv_padic_of_bounded hf_restr_nontriv h_restr_bdd with ⟨q, h1, h2⟩
  rcases h1 with ⟨hq, h3⟩
  rcases h3 with ⟨c, hcpos, hc⟩ -/
  let c := - (Real.logb p' (f π))
  have hcpos : 0 < c := by
    simp only [Left.neg_pos_iff, c]
    exact Real.logb_neg (mod_cast (Nat.Prime.one_lt hp_prime'))
      (map_pos_of_ne_zero f ( RingOfIntegers.coe_ne_zero_iff.mpr hpi_nezero)) hπ_f_lt_one
  have MulRingNorm_eq_one_of_Padic_eq_one (x : K) (h_Padic_zero : mulRingNorm_Padic P x = 1) : f x = 1 := by
    -- TODO
    sorry
  constructor
  · --existence
    simp only
    apply MulRingNorm.equiv_symm
    use c
    refine ⟨hcpos, ?_⟩
    ext x
    by_cases hx : x = 0
    · rw [hx]
      simp only [map_zero, le_refl]
      rw [Real.rpow_eq_zero (Preorder.le_refl 0) (Ne.symm (ne_of_lt hcpos))]
    · simp only [c, p']
      rw [mulRingNorm_Padic_eq_p_pow_valP P x hx,
        ← Real.rpow_intCast_mul (Nat.cast_nonneg' (prime_in_prime_ideal P)), mul_comm,
        Real.rpow_mul_intCast (Nat.cast_nonneg' (prime_in_prime_ideal P)),
        Real.rpow_neg (Nat.cast_nonneg' (prime_in_prime_ideal P)),
        Real.rpow_logb (mod_cast Nat.zero_lt_of_lt hp_gt_one) (mod_cast Nat.Prime.ne_one hp_prime')
        hπ_f_gt_zero]
      simp only [zpow_neg, inv_zpow', inv_inv]


      rw [← div_eq_one_iff_eq, ← map_zpow₀]
      sorry
      sorry
  · --uniqueness
    intro Q hQ
    sorry

end Nonarchimedean
