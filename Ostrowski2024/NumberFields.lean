import Mathlib
--import Ostrowski2024.NonArchimedean

/-!
# Ostrowski's theorem for number fields

## References
* https://kconrad.math.uconn.edu/blurbs/gradnumthy/ostrowskiQ.pdf
* https://kconrad.math.uconn.edu/blurbs/gradnumthy/ostrowskinumbfield.pdf

-/


section localization

namespace Set

noncomputable section

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

open scoped nonZeroDivisors

universe u v

variable
  {R : Type u} [CommRing R] [IsDedekindDomain R]
  (S : Set <| HeightOneSpectrum R)
  (K : Type v) [Field K] [Algebra R K] [IsFractionRing R K]


/-- The multiplicative set of non-zero elements avoiding all primes outside `S`.

Localizing at this set allows denominators which are units at every height-one prime
not belonging to `S`. -/
def MultiplicativeSet : Submonoid R := {
  carrier := (⋂ (v : HeightOneSpectrum R) (_ : v ∉ S), (v.asIdeal.carrier)ᶜ) ∩ (nonZeroDivisors R)
  mul_mem' := by
    -- Prime ideals outside `S` do not contain either factor, hence do not contain
    -- their product. The non-zero-divisor condition is closed under multiplication.
    rintro _ _ ⟨ha, ha0⟩ ⟨hb, hb0⟩
    simp only [mem_iInter, mem_inter_iff] at ha hb ⊢
    exact ⟨fun v hv ↦ v.isPrime.mul_notMem (ha v hv) (hb v hv), (nonZeroDivisors R).mul_mem ha0 hb0⟩
  one_mem' := by simpa using fun i (_ : i ∉ S) ↦ i.asIdeal.one_notMem
}


/-- The ring of elements integral away from `S` is the localization of `R` at
`S.MultiplicativeSet`.

This is a standard description of rings of `S`-integers in a Dedekind domain when
the class group is torsion. -/
instance IsLocalization_Sint [Fact (Monoid.IsTorsion (ClassGroup R))] :
    IsLocalization S.MultiplicativeSet <| S.integer K where
  map_units := sorry
  surj := sorry
  exists_of_eq := sorry

end

end Set

end localization


open IsDedekindDomain HeightOneSpectrum WithZeroMulInt NumberField NNReal

variable {K : Type*} [Field K] [nf : NumberField K] (f : AbsoluteValue K ℝ)

section Nonarchimedean

open NumberField.RingOfIntegers.HeightOneSpectrum

/-- If the `v`-adic absolute value of `α` is at most one, then `α` can be written
as a quotient of algebraic integers with denominator a `v`-adic unit. -/
lemma exists_num_denom_absolute_value_one {α : K} {v : HeightOneSpectrum (𝓞 K)}
    {b : ℝ≥0} (hb : 1 < b) (h_abs : adicAbv v hb α ≤ 1) :
  ∃ x y : 𝓞 K, α = x / y ∧ adicAbv v hb (y : K) = 1 := by
  -- Allow denominators away from `v`, so the only condition to check is at `v`.
  let S : Set (HeightOneSpectrum (𝓞 K)) := {w | w ≠ v}
  have mem : α ∈ S.integer K := by
    refine (show ∀ w : HeightOneSpectrum (𝓞 K), w ∉ S → w.valuation K α ≤ 1 from ?_)
    intro w hw
    obtain rfl : w = v := by simpa [S] using hw
    exact (toNNReal_le_one_iff (e := b) hb).1 (by
      simpa [IsDedekindDomain.HeightOneSpectrum.adicAbv,
        IsDedekindDomain.HeightOneSpectrum.adicAbvDef] using h_abs)
  -- Use the localization description of `S`-integers to choose a numerator and
  -- denominator in `𝓞 K`.
  letI : Fact (Monoid.IsTorsion (ClassGroup (𝓞 K))) := fact_iff.mpr isTorsion_of_finite
  letI : IsLocalization S.MultiplicativeSet (S.integer K) := Set.IsLocalization_Sint S K
  let γ : S.integer K := ⟨α, mem⟩
  obtain ⟨⟨x, ⟨y, hy_away, hy_nzd⟩⟩, hxy⟩ := IsLocalization.surj S.MultiplicativeSet γ
  refine ⟨x, y, ?_, ?_⟩
  · have hxK : α * (y : K) = x := by
      simpa [γ] using congrArg (fun z : S.integer K => (z : K)) hxy
    -- The denominator lies in the chosen multiplicative set, hence is non-zero.
    have hy_ne_zero : (y : K) ≠ 0 :=
      RingOfIntegers.coe_ne_zero_iff.mpr (nonZeroDivisors.ne_zero hy_nzd)
    exact (eq_div_iff hy_ne_zero).2 hxK
  · have hy_not_mem : y ∉ v.asIdeal := by
      -- Since `v ∉ S`, the denominator avoids the prime ideal corresponding to `v`.
      have hy_not_mem_all :
          ∀ w : HeightOneSpectrum (𝓞 K), w ∉ S → (y : 𝓞 K) ∉ w.asIdeal := by
        simpa [Set.mem_iInter] using hy_away
      exact hy_not_mem_all v (by simp [S])
    exact (adicAbv_coe_eq_one_iff (v := v) (hb := hb) (r := y)).2 hy_not_mem

variable (nonarch : ∀ x y : K, f (x + y) ≤ max (f x) (f y))

open Polynomial minpoly

include nonarch in
/-- Algebraic integers are contained in the closed unit ball of a nonarchimedean
absolute value. -/
lemma integers_closed_unit_ball (x : 𝓞 K) : f x ≤ 1 := by
  -- First remove the zero case.
  by_cases h : x = (0 : K); simp [h]
  let P := minpoly ℤ x
  -- The minimal polynomial is nonconstant because `x` is integral.
  have hnezerodeg : P.natDegree ≠ 0 := by
    linarith [minpoly.natDegree_pos <| RingOfIntegers.isIntegral x]
  -- Rearrange `P(x) = 0` to express the leading power as a sum of lower powers.
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
  -- If `f x > 1`, the ultrametric estimate bounds the leading power by the
  -- largest lower power, contradicting strict monotonicity of powers above one.
  have hineq4 : (f x) ^ P.natDegree ≤ (f x) ^ (P.natDegree - 1) := by
    nth_rewrite 1 [← map_pow, ← map_pow, hminp]
    simp only [Finset.sum_neg_distrib, map_neg, map_sum, map_mul, map_intCast, map_pow,
      map_neg_eq_map]
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
/-- The open unit ball in `𝓞 K` is a non-zero prime ideal of `𝓞 K`. -/
def prime_ideal (hf_nontriv : f.IsNontrivial) : IsDedekindDomain.HeightOneSpectrum (𝓞 K) where
  asIdeal := {
    carrier := {a : (𝓞 K) | f a < 1}
    add_mem' := by
                  -- The ultrametric inequality makes the open unit ball additively closed.
                  simp only [Set.mem_setOf_eq, map_add]
                  exact fun ha hb ↦ lt_of_le_of_lt (nonarch _ _) (max_lt ha hb)
    zero_mem' := by simp
    smul_mem' := by
                  -- Algebraic integers have absolute value at most one, so multiplying by
                  -- an algebraic integer preserves the open unit ball.
                  simp only [Set.mem_setOf_eq, smul_eq_mul, map_mul]
                  exact fun c x hx ↦ mul_lt_one_of_nonneg_of_lt_one_right
                    (integers_closed_unit_ball f nonarch c) (apply_nonneg f ↑x) hx
  }
  isPrime := by
      rw [Ideal.isPrime_iff]
      constructor
      -- The open unit ball is proper because `1` has absolute value `1`.
      · simp [-ne_eq, -AddSubsemigroup.mk_eq_top, Ideal.ne_top_iff_one]
      -- If `x * y` has absolute value less than `1`, one of the two factors must.
      · simp only [Submodule.mem_mk, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk,
        Set.mem_setOf_eq, map_mul]
        intro x y hxy
        by_contra! h
        linarith [one_le_mul_of_one_le_of_one_le h.1 h.2]
  ne_bot := by
      -- Nontriviality gives an element with absolute value different from `1`.
      -- Writing it as a fraction of algebraic integers shows that one of the
      -- numerator or denominator lies in the open unit ball.
      rw [Submodule.ne_bot_iff]
      simp only [Submodule.mem_mk, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk, Set.mem_setOf_eq,
        ne_eq]
      obtain ⟨a, ha, hfa⟩ := hf_nontriv
      obtain ⟨c, b, h3, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 K) a
      have h_b_nezero : b ≠ 0 := nonZeroDivisors.ne_zero h3
      by_cases h : f b < 1; exact ⟨b, h, h_b_nezero⟩
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
/-- A nontrivial nonarchimedean absolute value on a number field is uniquely equal
to an adic absolute value attached to a height-one prime of `𝓞 K`. -/
theorem Ostr_nonarch (hf_nontriv : f.IsNontrivial) :
    ∃! P : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
    ∃ b : ℝ≥0, ∃ hb : 1 < b,
    f = adicAbv P hb := by
  -- Let `P` be the height-one prime given by the open unit ball.
  let P := prime_ideal f nonarch hf_nontriv
  use P
  simp only [forall_exists_index]
  have h_norm := HeightOneSpectrum.one_lt_absNorm P
  -- Choose a uniformizer of `P`; its absolute value determines the base `b`.
  rcases IsDedekindDomain.HeightOneSpectrum.intValuation_exists_uniformizer P with ⟨π, hπ⟩
  -- Basic facts about the chosen uniformizer.
  have hπ_ne_zero : π ≠ 0 := by
    by_contra! h
    rw [h] at hπ
    simp at hπ
    have := @WithZero.exp_ne_zero ℤ 1
    contradiction
  have hπ_zero_le_f : 0 < f π := by simp [hπ_ne_zero]
  have hπ_f_lt_one : f π < 1 := by
    exact (show (π : 𝓞 K) ∈ P.asIdeal ↔ f (π : K) < 1 from Iff.rfl).1 <|
      (IsDedekindDomain.HeightOneSpectrum.intValuation_lt_one_iff_mem P π).1 <| by
        rw [hπ]
        rw [← WithZero.exp_zero, WithZero.exp_lt_exp]
        norm_num
  have hπ_val_ne_zero : P.valuation K (π : K) ≠ 0 := by simp_all
  have hπ_toAdd: Multiplicative.toAdd (WithZero.unzero hπ_val_ne_zero) = -1 := by
    simp_all [IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap P π, P]
    rfl
  -- Elements of `v`-adic absolute value `1` also have `f`-absolute value `1`.
  -- First reduce to algebraic integers using the denominator lemma above.
  have absolute_value_eq_one_of_vadic_abv_eq_one {x : K} (hx : x ≠ 0) {b : ℝ≥0} (hb : 1 < b)
      (h : adicAbv P hb x = 1) : f x = 1 := by
    obtain ⟨y, z, rfl, hz⟩ := exists_num_denom_absolute_value_one hb (le_of_eq h)
    have : y ≠ 0 ∧ z ≠ 0 := by
      by_contra! h'
      apply hx
      by_cases h'' : y = 0
      · simp_all
      · simp_all [h' h'']
    have absolute_value_eq_one_of_vadic_abv_eq_one_int {x : 𝓞 K} (hx : x ≠ 0) (h : adicAbv P hb (x : K) = 1) :
      f x = 1 := by
      -- For algebraic integers, being a `P`-adic unit means not lying in the
      -- open unit ball, and the closed unit ball lemma gives the reverse bound.
      rw [adicAbv_coe_eq_one_iff] at h
      have : 1 ≤ f x := le_of_not_gt h
      linarith [integers_closed_unit_ball f nonarch x]
    simp_all
  let b : ℝ≥0 := ⟨(f π)⁻¹, by positivity⟩
  have hb : 1 < b := by
    change (1 : ℝ) < (f π)⁻¹
    exact (one_lt_inv₀ hπ_zero_le_f).2 hπ_f_lt_one
  -- The chosen base makes the adic absolute value take the same value as `f` on
  -- the uniformizer.
  --let c := Real.logb (Ideal.absNorm P.asIdeal)⁻¹ (f π)
  constructor
  · use b, hb
    ext x
    by_cases hx : x = 0; simp [hx]
    -- Divide `x` by the matching power of the uniformizer. The quotient has
    -- `P`-adic absolute value `1`, so it has `f`-absolute value `1`.
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
  · -- Uniqueness: the prime is recovered as the set of algebraic integers with
    -- absolute value less than `1`.
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

end Nonarchimedean
