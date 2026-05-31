import Mathlib
--import Ostrowski2024.NonArchimedean

/-!
# Ostrowski's theorem for number fields

## References
* https://kconrad.math.uconn.edu/blurbs/gradnumthy/ostrowskiQ.pdf
* https://kconrad.math.uconn.edu/blurbs/gradnumthy/ostrowskinumbfield.pdf

-/

/-
section preliminaries1

variable {K : Type*} [Field K] {f : AbsoluteValue K ℝ}
  (nonarch : ∀ x y : K, f (x + y) ≤ max (f x) (f y))

-- TODO: check if needed or easier
open Finset in
include nonarch in
/-- ultrametric inequality with Finset.Sum  -/
lemma nonarch_sum_sup {α : Type*} {s : Finset α} (hnonempty : s.Nonempty) {l : α → K} :
    f (∑ i ∈ s, l i) ≤ s.sup' hnonempty fun i => f (l i) := by
  apply Nonempty.cons_induction (p := fun a hn ↦ f (∑ i ∈ a, l i) ≤ a.sup' hn fun i ↦ f (l i))
  · simp
  · intro a s h hs hind
    simp only [le_sup'_iff, mem_cons, sum_cons, exists_eq_or_imp]
    rw [← le_sup'_iff hs]
    have h := le_max_iff.mp <| nonarch (l a) (∑ i ∈ s, l i)
    rcases h with h₁ | h₂
    · exact .inl h₁
    · exact .inr <| le_trans h₂ hind

include nonarch in
lemma nonarch_nat_le_one (x : ℕ) : f x ≤ 1 := by
  by_cases h : x = 0; simp [h] -- first get rid of the case x = 0
  have : ∑ i ∈ Finset.range x, (1 : K) = x := by simp
  rw [← this]
  apply le_trans <| nonarch_sum_sup nonarch (by simp [h])
  simp

include nonarch in
lemma nonarch_int_le_one (x : ℤ) : f x ≤ 1 := by
  rw [← AbsoluteValue.apply_natAbs_eq]
  exact nonarch_nat_le_one nonarch x.natAbs

end preliminaries1
 -/
open IsDedekindDomain HeightOneSpectrum WithZeroMulInt NumberField NNReal

variable {K : Type*} [Field K] [nf : NumberField K] (f : AbsoluteValue K ℝ)

section Nonarchimedean

open NumberField.RingOfIntegers.HeightOneSpectrum

--The next lemma is a general fact in algebraic number theory.
--This might be complicated, Conrad uses the class group but we might try with norms or minimal polynomials
-- Here https://feog.github.io/antchap6.pdf is a proof without class group
lemma exists_num_denom_absolute_value_one {α : K} (h_nezero : α ≠ 0) {v : HeightOneSpectrum (𝓞 K)}
    {b :ℝ≥0} (hb : 1 < b) (h_abs : adicAbv v hb α ≤ 1) :
  ∃ x y : 𝓞 K, α = x / y ∧ adicAbv v hb (y : K) = 1 := by
  sorry

variable (nonarch : ∀ x y : K, f (x + y) ≤ max (f x) (f y))

open Polynomial minpoly

include nonarch in
/-- `𝓞 K` is contained in the closed unit ball -/
lemma integers_closed_unit_ball (x : 𝓞 K) : f x ≤ 1 := by
  by_cases h : x = (0 : K); simp [h] -- first get rid of the case x = 0
  -- now x ≠ 0
  let P := minpoly ℤ x
  -- P has positive degree
  have hnezerodeg : P.natDegree ≠ 0 := by
    linarith [minpoly.natDegree_pos <| RingOfIntegers.isIntegral x]
  -- Equality given by the minimal polynomial of x
  have hminp : x ^ P.natDegree = ∑ i ∈ Finset.range P.natDegree, -((P.coeff i) * x ^ i) := by
    have : x ^ P.natDegree = (P.coeff P.natDegree) * x ^ P.natDegree := by
      nth_rw 1 [← one_mul (x ^ P.natDegree), coeff_natDegree]
      congr
      exact_mod_cast (minpoly.monic <| NumberField.RingOfIntegers.isIntegral x).symm
    simp only [Finset.sum_neg_distrib, eq_neg_iff_add_eq_zero, ← aeval ℤ x, aeval_eq_sum_range,
      zsmul_eq_mul]
    rw [this]
    exact (Finset.sum_range_succ_comm (fun x_1 => ↑(P.coeff x_1) * x ^ x_1) P.natDegree).symm
  by_contra! hc
  have hineq4 : (f x) ^ P.natDegree ≤ (f x) ^ (P.natDegree - 1) := by
    nth_rewrite 1 [← map_pow, ← map_pow, hminp]
    simp only [Finset.sum_neg_distrib, map_neg, map_sum, map_mul, map_intCast, map_pow,
      map_neg_eq_map]
    /- rw [Finset.sum_range]
    simp_rw [← List.sum_ofFn]
    apply le_trans (AbsoluteValue.nonarch_sum_sup' nonarch)
    simp only [Option.getD, List.map_ofFn]
    split; swap; simp
     -/
    apply le_trans (IsNonarchimedean.apply_sum_le_sup nonarch (Finset.nonempty_range_iff.mpr hnezerodeg))
    apply Finset.sup'_le (Finset.nonempty_range_iff.mpr hnezerodeg)
    intro i hi
    rw [Finset.mem_range] at hi
    calc
      f ((↑(P.coeff i) * x ^ i))
        ≤ (f x) ^ i := by
        simp [mul_le_iff_le_one_left (pow_pos (f.pos h) i),
          IsNonarchimedean.apply_intCast_le_one nonarch]
      _ ≤ (f x) ^ (P.natDegree - 1) := (pow_le_pow_iff_right₀ hc).mpr <| Nat.le_sub_one_of_lt hi
  apply not_lt_of_ge hineq4
  gcongr
  grind

include nonarch in
/-- The open unit ball in 𝓞 K is a non-zero prime ideal of 𝓞 K. -/
def prime_ideal (hf_nontriv : f.IsNontrivial) : IsDedekindDomain.HeightOneSpectrum (𝓞 K) where
  asIdeal := {
    carrier := {a : (𝓞 K) | f a < 1}
    add_mem' := by
                  simp only [Set.mem_setOf_eq, map_add]
                  exact fun ha hb ↦ lt_of_le_of_lt (nonarch _ _) (max_lt ha hb)
    zero_mem' := by simp
    smul_mem' := by
                  simp only [Set.mem_setOf_eq, smul_eq_mul, map_mul]
                  exact fun c x hx ↦ mul_lt_one_of_nonneg_of_lt_one_right
                    (integers_closed_unit_ball f nonarch c) (apply_nonneg f ↑x) hx
  }
  isPrime := by
      rw [Ideal.isPrime_iff]
      constructor
      -- P is not 𝓞 K:
      · simp [-ne_eq, -AddSubsemigroup.mk_eq_top, Ideal.ne_top_iff_one]
      -- x * y ∈ P → x ∈ P ∨ y ∈ P:
      · simp only [Submodule.mem_mk, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk,
        Set.mem_setOf_eq, map_mul]
        intro x y hxy
        by_contra! h
        linarith [one_le_mul_of_one_le_of_one_le h.1 h.2]
  ne_bot := by
      -- P ≠ 0
      rw [Submodule.ne_bot_iff]
      simp only [Submodule.mem_mk, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk, Set.mem_setOf_eq,
        ne_eq]
      obtain ⟨a, ha, hfa⟩ := hf_nontriv
      obtain ⟨c, b, h3, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 K) a
      have h_b_nezero : b ≠ 0 := nonZeroDivisors.ne_zero h3
      by_cases h : f b < 1; exact ⟨b, h, h_b_nezero⟩ --if f b < 1, we are done
      have h_c_nezero : c ≠ 0 := by
        by_contra! h
        simp [h] at ha
      have h_b : f b = 1 := by linarith [integers_closed_unit_ball f nonarch b]
      simp only [map_div₀, h_b, div_one, ne_eq] at hfa
      have h_c_lt_one : f c < 1 := by
        linarith [lt_of_le_of_ne (integers_closed_unit_ball f nonarch c) hfa]
      exact ⟨c, h_c_lt_one, h_c_nezero⟩

--TODO: clean up
open AbsoluteValue in
include nonarch in
theorem Ostr_nonarch (hf_nontriv : f.IsNontrivial) :
    ∃! P : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
    ∃ b : ℝ≥0, ∃ hb : 1 < b,
    f = adicAbv P hb := by
  -- get the ideal P (open unit ball in 𝓞 K)
  let P := prime_ideal f nonarch hf_nontriv
  use P
  simp only [forall_exists_index]
  have h_norm := HeightOneSpectrum.one_lt_absNorm P
  --uniformizer of P, this gives the constant c
  rcases IsDedekindDomain.HeightOneSpectrum.intValuation_exists_uniformizer P with ⟨π, hπ⟩
  --Some useful facts about π
  have hπ_ne_zero : π ≠ 0 := by
    by_contra! h
    rw [h] at hπ
    simp at hπ
    have := @WithZero.exp_ne_zero ℤ 1
    contradiction
  have hπ_zero_le_f : 0 < f π := by simp [hπ_ne_zero]
  have hπ_f_lt_one : f π < 1 := by
    convert_to  π ∈ P.asIdeal.carrier
    simp only [AddSubsemigroup.mem_carrier, AddSubmonoid.mem_toSubsemigroup,
      Submodule.mem_toAddSubmonoid, ← Ideal.dvd_span_singleton,
      ← IsDedekindDomain.HeightOneSpectrum.intValuation_lt_one_iff_dvd, hπ]
    norm_cast
  have hπ_val_ne_zero : P.valuation K (π : K) ≠ 0 := by simp_all
  have hπ_toAdd: Multiplicative.toAdd (WithZero.unzero hπ_val_ne_zero) = -1 := by
    simp_all [IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap P π, P]
    rfl
  have absolute_value_eq_one_of_vadic_abv_eq_one {x : K} (hx : x ≠ 0) {b : ℝ≥0} (hb : 1 < b)
      (h : adicAbv P hb x = 1) : f x = 1 := by
    obtain ⟨y, z, rfl, hz⟩ := exists_num_denom_absolute_value_one hx hb (le_of_eq h)
    have : y ≠ 0 ∧ z ≠ 0 := by
      by_contra! h'
      apply hx
      by_cases h'' : y = 0
      · simp_all
      · simp_all [h' h'']
    have absolute_value_eq_one_of_vadic_abv_eq_one_int {x : 𝓞 K} (hx : x ≠ 0) (h : adicAbv P hb (x : K) = 1) :
      f x = 1 := by
      rw [adicAbv_coe_eq_one_iff] at h
      have : 1 ≤ f x := le_of_not_gt h
      linarith [integers_closed_unit_ball f nonarch x]
    simp_all
  let b : ℝ≥0 := ⟨(f π)⁻¹, by positivity⟩
  have hb : 1 < b := by
    change (1 : ℝ) < (f π)⁻¹
    exact (one_lt_inv₀ hπ_zero_le_f).2 hπ_f_lt_one
  -- the exponent such that (vadicAbv P x) ^ c = f x
  --let c := Real.logb (Ideal.absNorm P.asIdeal)⁻¹ (f π)
  /- have hcpos : 0 < c := Real.logb_pos_of_base_lt_one
    (inv_pos.mpr (mod_cast Nat.zero_lt_of_lt h_norm))
    (inv_lt_one_of_one_lt₀ <| mod_cast h_norm) hπ_zero_le_f hπ_f_lt_one -/
  constructor
  · use b, hb
    ext x
    by_cases hx : x = 0; simp [hx]
    have hx_val_ne_zero : P.valuation K x ≠ 0 := (Valuation.ne_zero_iff (P.valuation K)).mpr hx
    have : (b : ℝ) = (f π)⁻¹ := rfl
    simp [IsDedekindDomain.HeightOneSpectrum.adicAbv, adicAbvDef]
    simp only [WithZeroMulInt.toNNReal_neg_apply _ hx_val_ne_zero, NNReal.coe_zpow, this]
    rw [← neg_neg <| Multiplicative.toAdd (WithZero.unzero hx_val_ne_zero), ← inv_zpow', inv_inv,
      ← map_zpow₀, ← mul_inv_eq_one₀ <| (AbsoluteValue.ne_zero_iff f).mpr <|
      zpow_ne_zero _ (RingOfIntegers.coe_ne_zero_iff.mpr hπ_ne_zero), ← map_inv₀, ← map_mul]
    rw [zpow_neg, inv_inv]
    apply absolute_value_eq_one_of_vadic_abv_eq_one (mul_ne_zero hx
      (zpow_ne_zero _ (RingOfIntegers.coe_ne_zero_iff.mpr hπ_ne_zero))) hb
    simp [IsDedekindDomain.HeightOneSpectrum.adicAbv, adicAbvDef, this,
      WithZeroMulInt.toNNReal_neg_apply _ hπ_val_ne_zero,
      WithZeroMulInt.toNNReal_neg_apply _ hx_val_ne_zero, hπ_toAdd]
    have hπf_ne_zero : f (π : K) ≠ 0 :=
      (AbsoluteValue.ne_zero_iff f).2 (RingOfIntegers.coe_ne_zero_iff.mpr hπ_ne_zero)
    simpa [zpow_neg] using
      inv_mul_cancel₀ (zpow_ne_zero (Multiplicative.toAdd (WithZero.unzero hx_val_ne_zero)) hπf_ne_zero)
  · --uniqueness
    intro Q c hc heq
    simp [IsDedekindDomain.HeightOneSpectrum.ext_iff, ← SetLike.coe_set_eq, Set.ext_iff]
    intro x
    constructor
    · intro hxQ
      have hQlt : adicAbv Q hc (x : K) < 1 :=
        (adicAbv_coe_lt_one_iff (v := Q) (hb := hc) (r := x)).2 hxQ
      have hflt : f x < 1 := by simpa [heq] using hQlt
      exact (show x ∈ P.asIdeal ↔ f x < 1 by rfl).2 hflt
    · intro hxP
      have hflt : f x < 1 := (show x ∈ P.asIdeal ↔ f x < 1 by rfl).1 hxP
      have hQlt : adicAbv Q hc (x : K) < 1 := by simpa [heq] using hflt
      exact (adicAbv_coe_lt_one_iff (v := Q) (hb := hc) (r := x)).1 hQlt
    --rw [isEquiv_iff_exists_rpow_eq] at hQ
    --obtain ⟨c', hc'pos, heq⟩ := hQ
    /- rw [funext_iff] at heq
    specialize heq x
    rw [show x ∈ P.asIdeal ↔ f x < 1 by rfl,
      ← Real.rpow_lt_one_iff' (AbsoluteValue.nonneg f ↑x) hc'pos, heq,
      ← NumberField.FinitePlace.norm_lt_one_iff_mem, NumberField.FinitePlace.norm_def] -/

end Nonarchimedean
