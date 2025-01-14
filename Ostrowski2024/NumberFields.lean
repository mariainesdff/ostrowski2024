import Mathlib

/-!
# Ostrowski's theorem for number fields

## References
* https://kconrad.math.uconn.edu/blurbs/gradnumthy/ostrowskiQ.pdf
* https://kconrad.math.uconn.edu/blurbs/gradnumthy/ostrowskinumbfield.pdf

-/

open NumberField

variable {K : Type*} [Field K] [nf : NumberField K]  (f : AbsoluteValue K ℝ)

section Nonarchimedean

namespace IsDedekindDomain.HeightOneSpectrum

variable (P : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) -- P is a nonzero prime ideal of 𝓞 K

lemma val_zero (a : K) : P.valuation a = 0 → a = 0 := (Valuation.zero_iff P.valuation).mp

lemma val_ne_zero (a : K) (h : P.valuation a ≠ 0 ) : a ≠ 0 := by simp_all

lemma hcard : 1 ≤ ((Nat.card (𝓞 K ⧸ P.asIdeal)) : ℝ) := by
  norm_cast
  have hfin := Fintype.finite (Ideal.fintypeQuotientOfFreeOfNeBot P.asIdeal P.ne_bot)
  exact Nat.one_le_iff_ne_zero.mpr (Nat.card_ne_zero.mpr ⟨instNonemptyOfInhabited, hfin⟩)

/-- A non zero prime ideal of 𝓞 K contains a unique prime number -/
lemma exist_prime_in_prime_ideal : ∃! (p : ℕ), ∃ (_ : Fact (p.Prime)), (↑p ∈ P.asIdeal) := by
  let r := Ideal.absNorm P.asIdeal
  set k := 𝓞 K ⧸ P.asIdeal
  have : Field k := Ideal.Quotient.field P.asIdeal
  have : Fintype k := Ideal.fintypeQuotientOfFreeOfNeBot P.asIdeal P.ne_bot
  rcases FiniteField.card' k with ⟨p, n, hp, hcard⟩
  have : r = p ^ (n : ℕ) := by
    rw [← hcard]
    simp only [r, k, Ideal.absNorm_apply, Submodule.cardQuot_apply,  Nat.card_eq_fintype_card]
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
    --if p and q are different, they are coprime and therefore P contains 1
    rw [← Nat.coprime_primes hq1.out hp,← Nat.isCoprime_iff_coprime] at hpq
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
--properties of such p
lemma prime_in_prime_ideal_is_prime : Fact ((prime_in_prime_ideal P).Prime) := (Exists.choose_spec (exist_prime_in_prime_ideal P)).1.1

lemma prime_in_prime_ideal_is_in_prime_ideal : (↑(prime_in_prime_ideal P) ∈ P.asIdeal) := (Exists.choose_spec (exist_prime_in_prime_ideal P)).1.2

lemma p_ne_zero (p : ℕ) (hp : Fact (p.Prime)) : (p : NNReal) ≠ 0 := by
  simp only [ne_eq, Nat.cast_eq_zero]
  exact NeZero.ne p

lemma one_lt_p (p : ℕ) (hp : Fact (p.Prime)) : 1 < (p : NNReal) := mod_cast Nat.Prime.one_lt (Fact.elim hp)


end IsDedekindDomain.HeightOneSpectrum

-- end examples

--The next lemma is a general fact in algebraic number theory.
--This might be complicated, Conrad uses the class group but we might try with norms or minimal polynomials
open NumberField in
lemma exists_num_denom_absolute_value_one (α : K) (h_nezero : α ≠ 0)
    (h_abs : vadicAbv v α ≤ 1) : ∃ x y : 𝓞 K, α = x / y ∧ FinitePlace.mk v y = 1 := by
    sorry

variable (nonarch : ∀ x y : K, f (x + y) ≤ max (f x) (f y))

-- TODO: check if needed or easier
include nonarch in
/-- ultrametric inequality with Finset.Sum  -/
lemma nonarch_sum_sup (α : Type*) (s : Finset α) (hnonempty : s.Nonempty) (l : α → K) : f (∑ i ∈ s, l i) ≤
  s.sup' hnonempty fun i => f (l i) := by
  let p : (a : Finset α) → Finset.Nonempty a → Prop := fun a hn => f (∑ i ∈ a, l i) ≤ a.sup' hn fun i => f (l i)
  convert_to p s hnonempty
  apply Finset.Nonempty.cons_induction
  · simp only [Finset.le_sup'_iff, Finset.mem_singleton, Finset.sum_singleton, exists_eq_left,
    le_refl, implies_true, p]
  · intro a s h hs hind
    simp only [Finset.le_sup'_iff, Finset.mem_cons, Finset.sum_cons, exists_eq_or_imp, p]
    rw [← Finset.le_sup'_iff hs]
    --should be easy to finish
    sorry

open Polynomial minpoly

--TODO: Check and clean
include nonarch in
/-- 𝓞 K is contained in the closed unit ball -/
lemma integers_closed_unit_ball (x : 𝓞 K) : f x ≤ 1 := by
  by_cases h : x = (0 : K) -- first get rid of the case x = 0
  rw [h, map_zero f]
  exact zero_le_one' ℝ
  -- now x ≠ 0
  let P := minpoly ℤ x
  -- Equality given by the minimal polynomial of x
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
    -- use that f is bounded by 1 on ℤ
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
    have hx : IsIntegral ℤ x := RingOfIntegers.isIntegral x
    have := minpoly.natDegree_pos hx
    linarith
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

include nonarch in
/-- The open unit ball in 𝓞 K is a non-zero prime ideal of 𝓞 K. -/
lemma exists_ideal [DecidableEq K] (hf_nontriv : f.IsNontrivial) :
    ∃ P : IsDedekindDomain.HeightOneSpectrum (𝓞 K), {a : (𝓞 K) | f a < 1} = P.asIdeal.carrier := by
  use
  { asIdeal := {carrier   := {a : (𝓞 K) | f a < 1}
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
      simp only [AbsoluteValue.IsNontrivial] at hf_nontriv
     /-  apply hf_nontriv
      simp only [Submodule.mem_mk, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk, Set.mem_setOf_eq] at h
      refine MulRingNorm.ext_iff.mpr ?_
      simp only [MulRingNorm.apply_one]
      intro x -/
      sorry
  }

include nonarch in
theorem Ostr_nonarch [DecidableEq K] (hf_nontriv : f.IsNontrivial) :
    ∃! P : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
    f ≈ vadicAbv P := by
  rcases exists_ideal f nonarch hf_nontriv with ⟨P, hP⟩ -- get the ideal P (open unit ball in 𝓞 K)
  rcases IsDedekindDomain.HeightOneSpectrum.intValuation_exists_uniformizer P with ⟨π, hπ⟩ --uniformizer of P, this gives the constant c
  --some properties of π used later
  have hpi_nezero : π ≠ 0 := by
    by_contra! h
    rw [h] at hπ
    simp only [IsDedekindDomain.HeightOneSpectrum.intValuationDef_zero, Int.reduceNeg, ofAdd_neg,
      WithZero.coe_inv, zero_eq_inv, WithZero.zero_ne_coe] at hπ
  have hπ_val : P.intValuationDef π < 1 := by --prob needed in hπ_f_lt_one, or maybe not
    rw [hπ]
    exact Batteries.compareOfLessAndEq_eq_lt.mp rfl
  have hπ_f_gt_zero : 0 < f π := by
    sorry
  have hπ_f_lt_one : f π < 1 := by
    sorry
  use P
  --get the prime number p inside P
  let p := IsDedekindDomain.HeightOneSpectrum.prime_in_prime_ideal P
  --some properties of p
  have hp_prime_fact : Fact (Nat.Prime p) := IsDedekindDomain.HeightOneSpectrum.prime_in_prime_ideal_is_prime P
  have hp_prime := hp_prime_fact.elim
  have hPmem' : ↑p ∈ P.asIdeal := IsDedekindDomain.HeightOneSpectrum.prime_in_prime_ideal_is_in_prime_ideal P
  have hp_gt_one : 1 < p := by exact Nat.Prime.one_lt hp_prime
  have h_abv_pi : (vadicAbv P) ↑π = (p : ℝ)⁻¹ := by --this is false, ramification index is needed
    /- rw [mulRingNorm_Padic_eq_p_pow_valP P π (RingOfIntegers.coe_ne_zero_iff.mpr hpi_nezero)]
    unfold val_P -- make a lemma val_PDef
    simp only [neg_neg, p]
    rw [← zpow_neg_one]
    congr
    simp_rw [IsDedekindDomain.HeightOneSpectrum.valuation_eq_intValuationDef P π, hπ]
    simp only [Int.reduceNeg, ofAdd_neg, WithZero.coe_inv, WithZero.unzero_coe, toAdd_inv,
      toAdd_ofAdd] -/
    sorry
  -- this is our constant giving the equivalence of MulRingNorm
  let c := - (Real.logb p (f π)) --not sure about this
  have hcpos : 0 < c := by
    simp only [Left.neg_pos_iff, c]
    exact Real.logb_neg (mod_cast (Nat.Prime.one_lt hp_prime))
      (map_pos_of_ne_zero f ( RingOfIntegers.coe_ne_zero_iff.mpr hpi_nezero)) hπ_f_lt_one
  have abv_eq_one_of_Padic_eq_one (x : K) (h_Padic_zero : vadicAbv P x = 1) : f x = 1 := by
    -- TODO
    sorry
  constructor
  · --existence
    sorry
    /- simp only [AbsoluteValue.IsEquiv]
    apply AbsoluteValue.isEquiv_symm -/
    /- use c
    refine ⟨hcpos, ?_⟩
    ext x
    by_cases hx : x = 0
    · simp only [hx, map_zero, le_refl,
        Real.rpow_eq_zero (Preorder.le_refl 0) (Ne.symm (ne_of_lt hcpos))]
    · simp only [c, p]
      rw [mulRingNorm_Padic_eq_p_pow_valP P x hx,
        ← Real.rpow_intCast_mul (Nat.cast_nonneg' (prime_in_prime_ideal P)), mul_comm,
        Real.rpow_mul_intCast (Nat.cast_nonneg' (prime_in_prime_ideal P)),
        Real.rpow_neg (Nat.cast_nonneg' (prime_in_prime_ideal P)),
        Real.rpow_logb (mod_cast Nat.zero_lt_of_lt hp_gt_one) (mod_cast Nat.Prime.ne_one hp_prime)
        hπ_f_gt_zero]
      simp only [zpow_neg, inv_zpow', inv_inv]
      rw [← mul_inv_eq_one₀ ((_root_.map_ne_zero f).mpr hx),← map_inv₀, ← map_zpow₀, ← map_mul]
      apply MulRingNorm_eq_one_of_Padic_eq_one
      simp only [map_mul, map_zpow₀, map_inv₀]
      rw [mulRingNorm_Padic_eq_p_pow_valP P x hx, h_mulRingNormPadic_pi]
      simp only [inv_zpow', zpow_neg, inv_inv]
      rw [inv_mul_eq_one₀]
      apply zpow_ne_zero
      exact Ne.symm (NeZero.ne' (p : ℝ)) -/
  · --uniqueness
    intro Q hQ
    sorry

end Nonarchimedean
