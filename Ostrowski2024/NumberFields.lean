import Mathlib

/-!
# Ostrowski's theorem for number fields

## References
* https://kconrad.math.uconn.edu/blurbs/gradnumthy/ostrowskiQ.pdf
* https://kconrad.math.uconn.edu/blurbs/gradnumthy/ostrowskinumbfield.pdf

-/


section preliminaries1

variable {K : Type*} [Field K] {f : AbsoluteValue K ℝ}
  (nonarch : ∀ x y : K, f (x + y) ≤ max (f x) (f y))

-- TODO: check if needed or easier
open Finset in
include nonarch in
/-- ultrametric inequality with Finset.Sum  -/
lemma nonarch_sum_sup {α : Type*} {s : Finset α} (hnonempty : s.Nonempty) (l : α → K) :
    f (∑ i ∈ s, l i) ≤ s.sup' hnonempty fun i => f (l i) := by
  apply Nonempty.cons_induction (p := fun a hn ↦ f (∑ i ∈ a, l i) ≤ a.sup' hn fun i ↦ f (l i))
  · simp
  · intro a s h hs hind
    simp only [le_sup'_iff, mem_cons, sum_cons, exists_eq_or_imp]
    rw [← le_sup'_iff hs]
    have h := nonarch (l a) (∑ i ∈ s, l i)
    rw [le_max_iff] at h
    rcases h with h₁ | h₂
    · exact .inl h₁
    · exact .inr <| le_trans h₂ hind

end preliminaries1

open NumberField

variable {K : Type*} [Field K] [nf : NumberField K] (f : AbsoluteValue K ℝ)

section Nonarchimedean

--The next lemma is a general fact in algebraic number theory.
--This might be complicated, Conrad uses the class group but we might try with norms or minimal polynomials
lemma exists_num_denom_absolute_value_one (α : K) (h_nezero : α ≠ 0)
    (h_abs : vadicAbv v α ≤ 1) : ∃ x y : 𝓞 K, α = x / y ∧ vadicAbv v y = 1 := by
  sorry

variable (nonarch : ∀ x y : K, f (x + y) ≤ max (f x) (f y))

open Polynomial minpoly

--TODO: Check and clean
include nonarch in
/-- `𝓞 K` is contained in the closed unit ball -/
lemma integers_closed_unit_ball (x : 𝓞 K) : f x ≤ 1 := by
  by_cases h : x = (0 : K); simp [h] -- first get rid of the case x = 0
  -- now x ≠ 0
  let P := minpoly ℤ x
  -- Equality given by the minimal polynomial of x
  have hminp : x ^ P.natDegree = ∑ i ∈ Finset.range P.natDegree, -((P.coeff i) * x ^ i) := by
    simp only [Finset.sum_neg_distrib, eq_neg_iff_add_eq_zero]
    have heval : (aeval x) P = 0 := aeval ℤ x
    have hlcoeff1 : (P.coeff P.natDegree) = 1 := by
      simp only [coeff_natDegree]
      exact minpoly.monic <| NumberField.RingOfIntegers.isIntegral x
    simp only [← heval, aeval_eq_sum_range, zsmul_eq_mul]
    have : x ^ P.natDegree = (P.coeff P.natDegree) * x ^ P.natDegree := by
      simp [hlcoeff1]
    rw [this]
    exact Eq.symm (Finset.sum_range_succ_comm (fun x_1 => ↑(P.coeff x_1) * x ^ x_1) P.natDegree)
  have hineq1 : ∀ i ∈ Finset.range P.natDegree, f (-(↑(P.coeff i) * x ^ i)) ≤ (f x) ^ i := by
    intro i hi
    simp_all only [map_neg_eq_map, AbsoluteValue.map_mul, AbsoluteValue.map_pow,
      AbsoluteValue.pos_iff, ne_eq, not_false_eq_true, pow_pos, mul_le_iff_le_one_left]
    -- use that f is bounded by 1 on ℤ

    --add a lemma in FinitePlaces.lean: already made a PR
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
      nonarch_sum_sup nonarch
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
lemma exists_ideal (hf_nontriv : f.IsNontrivial) :
    ∃ P : IsDedekindDomain.HeightOneSpectrum (𝓞 K), {a : (𝓞 K) | f a < 1} = P.asIdeal.carrier := by
  use {
    asIdeal := {carrier   := {a : (𝓞 K) | f a < 1}
                add_mem'  := by
                  simp only [Set.mem_setOf_eq, map_add]
                  exact fun ha hb ↦ lt_of_le_of_lt (nonarch _ _) (max_lt ha hb)
                zero_mem' := by simp
                smul_mem' := by
                  simp only [Set.mem_setOf_eq, smul_eq_mul, map_mul]
                  exact fun c x hx ↦ Right.mul_lt_one_of_le_of_lt_of_nonneg
                    (integers_closed_unit_ball f nonarch c) hx (apply_nonneg f ↑x)
                }
    isPrime := by
      rw [Ideal.isPrime_iff]
      constructor
      -- P is not 𝓞 K:
      · simp [Ideal.ne_top_iff_one]
      -- x * y ∈ P → x ∈ P ∨ y ∈ P:
      · simp only [Submodule.mem_mk, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk,
        Set.mem_setOf_eq, map_mul]
        intro x y hxy
        by_contra! h
        linarith [one_le_mul_of_one_le_of_one_le h.1 h.2]
    ne_bot  := by
      -- P ≠ 0
      rw [Submodule.ne_bot_iff]
      simp only [Submodule.mem_mk, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk, Set.mem_setOf_eq,
        ne_eq]
      obtain ⟨a, ha, hfa⟩ := hf_nontriv
      obtain ⟨c, b, h3, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 K) a
      have h_b_nezero : b ≠ 0 := nonZeroDivisors.ne_zero h3
      by_cases h : f b < 1
      refine ⟨b, h, h_b_nezero⟩
      have h_c_nezero : c ≠ 0 := by
        by_contra! h
        simp [h] at ha
      have h_b : f b = 1 := by linarith [(integers_closed_unit_ball f nonarch b)]
      simp only [map_div₀, h_b, div_one, ne_eq] at hfa
      have h_c_lt_one : f c < 1 := by
        linarith [lt_of_le_of_ne (integers_closed_unit_ball f nonarch c) hfa]
      exact ⟨c, h_c_lt_one, h_c_nezero⟩
  }

include nonarch in
theorem Ostr_nonarch (hf_nontriv : f.IsNontrivial) :
    ∃! P : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
    f ≈ vadicAbv P := by
  -- get the ideal P (open unit ball in 𝓞 K)
  rcases exists_ideal f nonarch hf_nontriv with ⟨P, hP⟩
  have h_norm := one_lt_norm P
  --uniformizer of P, this gives the constant c
  rcases IsDedekindDomain.HeightOneSpectrum.intValuation_exists_uniformizer P with ⟨π, hπ⟩
  have hπ_zero : π ≠ 0 := by
    by_contra! h
    simp [h] at hπ
  have hπ_f_gt_zero : 0 < f π := by simp [hπ_zero]
  have hπ_f_lt_one : f π < 1 := by
    have : P.intValuationDef π < 1 := by
      rw [hπ]
      exact Batteries.compareOfLessAndEq_eq_lt.mp rfl
    have : π ∈ P.asIdeal.carrier := by
      rw [IsDedekindDomain.HeightOneSpectrum.intValuation_lt_one_iff_dvd] at this
      simp_all
    rw [← hP] at this
    exact this
  have hπ_ne_zero : P.valuation (π : K) ≠ 0 := by simp_all
  have hπint_ne_zero : P.intValuationDef π ≠ 0 := by simp_all
  have : Multiplicative.toAdd (WithZero.unzero hπint_ne_zero) = -1 := by
    have : -1 = Multiplicative.toAdd (Multiplicative.ofAdd (-1)) := rfl
    rw [this,
      ← WithZero.unzero_coe (x := Multiplicative.ofAdd (-1)) (by rw [← hπ]; exact hπint_ne_zero)]
    congr
  have hπ_abs_val: Multiplicative.toAdd (WithZero.unzero hπ_ne_zero) = -1 := by
    rw [← this]
    congr
    exact IsDedekindDomain.HeightOneSpectrum.valuation_eq_intValuationDef P π
  have absolute_value_eq_one_of_vadic_abv_eq_one_int {x : 𝓞 K} (hx : x ≠ 0) (h : vadicAbv P x = 1) :
    f x = 1 := by
    simp [← FinitePlace.norm_def, norm_eq_one_iff_not_mem] at h
    have : ¬ x ∈ P.asIdeal.carrier := h
    have : ¬ f x < 1 := by
      rw [← hP] at this
      exact this
    linarith [(integers_closed_unit_ball f nonarch x)]
  have absolute_value_eq_one_of_vadic_abv_eq_one {x : K} (hx : x ≠ 0) (h : vadicAbv P x = 1) : f x = 1 := by
    obtain ⟨y, z, rfl, hz⟩ := exists_num_denom_absolute_value_one x hx (le_of_eq h)
    have hz_ne_zero : z ≠ 0 := by
      by_contra! h
      rw [h] at hx
      apply hx
      simp
    have hy_ne_zero : y ≠ 0 := by
      by_contra! h
      rw [h] at hx
      apply hx
      simp
    rw [map_div₀, hz, div_one] at h
    rw [map_div₀, absolute_value_eq_one_of_vadic_abv_eq_one_int hy_ne_zero h,
      absolute_value_eq_one_of_vadic_abv_eq_one_int hz_ne_zero hz, div_one]
  use P
  simp only
  let c := Real.logb (Ideal.absNorm P.asIdeal)⁻¹ (f π)
  have hcpos : 0 < c := Real.logb_pos_of_base_lt_one (inv_pos.mpr (mod_cast Nat.zero_lt_of_lt h_norm))
    (inv_lt_one_of_one_lt₀ <| mod_cast h_norm) hπ_f_gt_zero hπ_f_lt_one
  constructor
  · apply AbsoluteValue.isEquiv_symm
    use c
    refine ⟨hcpos, ?_⟩
    ext x
    by_cases hx : x = 0; simp [hx, Real.rpow_eq_zero (le_refl 0) (ne_of_lt hcpos).symm]
    have hx_ne_zero : P.valuation x ≠ 0 := (Valuation.ne_zero_iff P.valuation).mpr hx
    simp only [Real.logb_inv, vadicAbv, AbsoluteValue.coe_mk, MulHom.coe_mk, c]
    rw [WithZeroMulInt.toNNReal_neg_apply _ hx_ne_zero]
    push_cast
    rw [← neg_neg <| Multiplicative.toAdd (WithZero.unzero hx_ne_zero), ← inv_zpow',
      ← Real.rpow_intCast_mul (by simp), mul_comm, Real.rpow_mul (by simp),
      Real.rpow_logb (by positivity) (inv_ne_one.mpr <| ne_of_gt (mod_cast h_norm)) hπ_f_gt_zero,
      ← mul_inv_eq_one₀ <| (AbsoluteValue.ne_zero_iff f).mpr hx, ← map_inv₀, Real.rpow_intCast,
      ← map_zpow₀, ← map_mul]
    apply absolute_value_eq_one_of_vadic_abv_eq_one
      <| mul_ne_zero (zpow_ne_zero (-Multiplicative.toAdd (WithZero.unzero hx_ne_zero))
      (RingOfIntegers.coe_ne_zero_iff.mpr hπ_zero)) (inv_ne_zero hx)
    rw [map_mul, map_zpow₀, map_inv₀, vadicAbv_def, WithZeroMulInt.toNNReal_neg_apply _ hπ_ne_zero]
    push_cast
    rw [← zpow_mul]
    rw [mul_neg, zpow_neg, hπ_abs_val, vadicAbv_def, WithZeroMulInt.toNNReal_neg_apply _ hx_ne_zero]
    simp only [Int.reduceNeg, neg_mul, one_mul, zpow_neg, inv_inv, NNReal.coe_zpow,
      NNReal.coe_natCast]
    apply CommGroupWithZero.mul_inv_cancel
    apply zpow_ne_zero
    positivity
  · --uniqueness
    intro Q hQ
    simp only [IsDedekindDomain.HeightOneSpectrum.ext_iff, ← Submodule.carrier_inj, ← hP,
      Set.ext_iff, AddSubsemigroup.mem_carrier, AddSubmonoid.mem_toSubsemigroup,
      Submodule.mem_toAddSubmonoid, Set.mem_setOf_eq]
    intro x
    obtain ⟨c', hc'pos, heq⟩ := hQ
    rw [funext_iff] at heq
    specialize heq x
    rw [← Real.rpow_lt_one_iff' (AbsoluteValue.nonneg f ↑x) hc'pos, heq,
      ← NumberField.norm_lt_one_iff_mem, NumberField.FinitePlace.norm_def]




/-
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
  /- let p := IsDedekindDomain.HeightOneSpectrum.prime_in_prime_ideal P
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
    sorry -/
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
    sorry -/

end Nonarchimedean
