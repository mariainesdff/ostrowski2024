--copy-pasted from mul_ring_norm in lean3


import Mathlib.NumberTheory.Padics.PadicNorm
import Ostrowski2024.Basic


import Mathlib.Order.Filter.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.Normed.Ring.Seminorm
import Mathlib.Data.Nat.Digits


/-!
# Ostrowski's theorem for ℚ

This file states some basic lemmas about mul_ring_norm ℚ

-/

noncomputable section

variable {f g : MulRingNorm ℚ}

-- TODO: remove this
-- I think this is a missing lemma in mathlib and maybe we can use this for now.
-- (Done)
--lemma f_mul_eq : mul_eq f := f.map_mul'

-- The norm of -1 is 1
-- (Done)
lemma norm_neg_one_eq_one : f (-1) = 1 := by
  simp only [map_neg_eq_map, map_one]


-- If x is non-zero, then the norm of x is larger than zero.
-- (Done)
lemma norm_pos_of_ne_zero {x : ℚ} (h : x ≠ 0) : f x > 0 := by
exact map_pos_of_ne_zero f h


--TODO: generalise to division rings, get rid of field_simp
-- (Done)
lemma ring_norm.div_eq (p : ℚ) {q : ℚ} : f (p / q) = (f p) / (f q) := by
exact map_div₀ f p q


-- This lemma look a bit strange to me.
-- (Done)
lemma int_norm_bound_iff_nat_norm_bound :
  (∀ n : ℕ, f n ≤ 1) ↔ (∀ z : ℤ, f z ≤ 1) := by
  constructor
  · intro h z
    obtain ⟨n,rfl | rfl ⟩ := Int.eq_nat_or_neg z
    · exact h n
    · simp only [Int.cast_neg, Int.cast_ofNat, map_neg_eq_map]
      exact h n
  · intro h n
    exact h n




lemma mul_eq_pow {a : ℚ} {n : ℕ} : f (a ^ n) = (f a) ^ n := by
  exact map_pow f a n



lemma NormRat_eq_on_Int_iff_eq_on_Nat : (∀ n : ℕ , f n = g n) ↔ (∀ n : ℤ , f n = g n) := by
  constructor
  · intro h z
    obtain ⟨n,rfl | rfl ⟩ := Int.eq_nat_or_neg z
    exact h n
    simp only [Int.cast_neg, Int.cast_ofNat, map_neg_eq_map]
    exact h n
  · exact fun a n => a ↑n


lemma NormRat_eq_iff_eq_on_Nat : (∀ n : ℕ , f n = g n) ↔ f = g := by
  constructor
  · intro h
    ext z
    have: ∃ n m : ℤ , z = n / m := by
      refine Rat.exists.mp ?_
      use z
    obtain ⟨ n , m, rfl⟩ := this
    rw [ring_norm.div_eq]
    rw [ring_norm.div_eq]
    rw [NormRat_eq_on_Int_iff_eq_on_Nat] at h
    rw [h,h]
  · intro h n
    exact congrFun (congrArg DFunLike.coe h) ↑n
