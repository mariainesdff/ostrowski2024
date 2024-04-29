--copy-pasted from mul_ring_norm in lean3


import Mathlib.NumberTheory.Padics.PadicNorm
import Ostrowski2024.Basic

import Mathlib.Data.Int.Cast.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.Normed.Ring.Seminorm
import Mathlib.Data.Nat.Digits


/-!
# Ostrowski's theorem for ℚ

This file states some basic lemmas about mul_ring_norm ℚ

-/

noncomputable section
variable {R : Type*} [Ring R]
variable {f g : MulRingNorm ℚ}

/-- The norm of -1 is 1 -/
--lemma norm_neg_one_eq_one {f : MulRingNorm R} : f (-1) = 1 := by simp only [map_neg_eq_map, map_one]

lemma f_of_abs_eq_f {f: MulRingNorm R} (x : ℤ) : f (Int.natAbs x) = f x := by
  obtain ⟨n,rfl|rfl⟩ := Int.eq_nat_or_neg x
  · simp only [Int.natAbs_ofNat, Int.cast_ofNat]
  · simp only [Int.natAbs_neg, Int.natAbs_ofNat, Int.cast_neg, Int.cast_ofNat, map_neg_eq_map]

-- I don't think this is needed anymore.
--lemma norm_pos_of_ne_zero {x : ℚ} (h : x ≠ 0) : f x > 0 := map_pos_of_ne_zero f h

-- I don't think this is needed anymore.
--lemma ring_norm.div_eq (p : ℚ) {q : ℚ} : f (p / q) = (f p) / (f q) := map_div₀ f p q

/- lemma int_norm_bound_iff_nat_norm_bound :
    (∀ n : ℕ, f n ≤ 1) ↔ (∀ z : ℤ, f z ≤ 1) := by
  refine' ⟨_, fun h n => h n⟩
  intro h z
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg z
  · exact h n
  · simp only [Int.cast_neg, Int.cast_ofNat, map_neg_eq_map]
    exact h n -/

lemma NormRat_eq_on_Int_iff_eq_on_Nat : (∀ n : ℕ , f n = g n) ↔ (∀ n : ℤ , f n = g n) := by
  refine' ⟨_, fun a n => a n⟩
  intro h z
  obtain ⟨n,rfl | rfl ⟩ := Int.eq_nat_or_neg z
  · exact h n
  · simp only [Int.cast_neg, Int.cast_ofNat, map_neg_eq_map]
    exact h n

lemma NormRat_eq_iff_eq_on_Nat : (∀ n : ℕ , f n = g n) ↔ f = g := by
  refine' ⟨_, fun h n => congrFun (congrArg DFunLike.coe h) ↑n⟩
  intro h
  ext z
  rw [← Rat.num_div_den z]
  simp only [map_div₀]
  rw [h, NormRat_eq_on_Int_iff_eq_on_Nat.mp h]

--this uses the definition of equivalence pushed in Mathlib
lemma NormRat_equiv_iff_equiv_on_Nat : (∃ c : ℝ, 0 < c ∧ (∀ n : ℕ , (f n)^c = g n)) ↔ f.equiv g:= by
  constructor
  · intro h
    obtain ⟨c, hc, h⟩ := h
    use c
    refine ⟨hc, ?_⟩
    ext x
    rw [← Rat.num_div_den x, map_div₀, map_div₀, Real.div_rpow (apply_nonneg f _) (apply_nonneg f _), h x.den,
      ← f_of_abs_eq_f,← f_of_abs_eq_f,h (Int.natAbs x.num)]
  · intro h
    obtain ⟨c, hc, h⟩ := h
    use c
    refine ⟨hc, ?_ ⟩
    intro n
    rw [← h]

/- --this is the precise formula needed in Ostrowski
lemma NormRat_equiv_iff_equiv_on_Nat (t : ℝ) : (∀ n : ℕ , (f n)^(t⁻¹) = g n) ↔ (∀ x : ℚ, (f x)^(t⁻¹) = g x) := by
  constructor
  · intro h x
    rw [← Rat.num_div_den x, map_div₀, map_div₀, Real.div_rpow, h x.den]
    · obtain ⟨n, hpos | hneg ⟩ := Int.eq_nat_or_neg x.num
      · rw [hpos]
        push_cast
        rw [h n]
      . rw [hneg]
        push_cast
        simp_rw [map_neg_eq_map, h n]
    all_goals exact apply_nonneg f _
  · intro hx n
    exact hx n

lemma NormRat_equiv_iff_equiv_on_Nat' (t : ℝ) : (∀ n : ℕ , (f n)^(t⁻¹) = g n) ↔ ( (fun x  : ℚ =>  (f x)^(t⁻¹)  )= g ) := by
  rw [NormRat_equiv_iff_equiv_on_Nat]
  exact Iff.symm Function.funext_iff
 -/
