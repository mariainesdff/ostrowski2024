/-
Copyright (c) 2024 María Inés de Frutos-Fernández, Filippo A. E. Nuccio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández, Filippo A. E. Nuccio
-/
import Mathlib.Algebra.Order.Group.TypeTags
import Mathlib.Data.NNReal.Basic
import Mathlib.Logic.Equiv.TransferInstance
import Mathlib.RingTheory.Valuation.Basic
import Mathlib.Tactic.Rify
/-!
# WithZero

In this file we provide some basic API lemmas for the `WithZero` construction and we define
the morphism `withZeroMultIntToNNReal`.

## Main Definitions

* `withZeroMultIntToNNReal` : The `MonoidWithZeroHom` from `ℤₘ₀ → ℝ≥0` sending `0 ↦ 0` and
  `x ↦ e^(Multiplicative.toAdd (WithZero.unzero hx)` when `x ≠ 0`, for a nonzero `e : ℝ≥0`.

## Main Results

* `withZeroMultIntToNNReal_strictMono` : The map `withZeroMultIntToNNReal` is strictly
   monotone whenever `1 < e`.


## Tags

WithZero, multiplicative, nnreal
-/


noncomputable section

open scoped  NNReal --DiscreteValuation

open Multiplicative WithZero Equiv

namespace Multiplicative

-- Mathlib.Algebra.Ring.Int
theorem ofAdd_pow_comm (a b : ℤ) : ofAdd a ^ b = ofAdd b ^ a := by
  rw [← Int.ofAdd_mul, mul_comm, Int.ofAdd_mul]

-- [Mathlib.Algebra.Group.TypeTags]
theorem ofAdd_inj {x y : Multiplicative ℤ} (hxy : ofAdd x = ofAdd y) : x = y := hxy

end Multiplicative

namespace WithZero

--[Mathlib.Algebra.Order.Ring.Cast, Mathlib.Data.NNRat.Defs, Mathlib.Algebra.Order.Ring.Abs]
theorem ofAdd_zpow (n : ℤ) : (↑(ofAdd n) : ℤₘ₀) = ofAdd (1 : ℤ) ^ n := by
  rw [← WithZero.coe_zpow, WithZero.coe_inj, ← Int.ofAdd_mul, one_mul]

--[Mathlib.Algebra.Order.Ring.Cast, Mathlib.Data.NNRat.Defs, Mathlib.Algebra.Order.Ring.Abs]
theorem ofAdd_zpow_zpow_comm (a b c : ℤ) : ((↑(ofAdd a) : ℤₘ₀) ^ b) ^ c = (ofAdd (a : ℤ) ^ c) ^ b := by
  simp only [← WithZero.coe_zpow]
  rw [← zpow_mul, mul_comm, zpow_mul]

--[Mathlib.Algebra.Order.Ring.Cast, Mathlib.Data.NNRat.Defs, Mathlib.Algebra.Order.Ring.Abs]
theorem ofAdd_neg_one_pow_comm (a : ℤ) (n : ℕ) :
    ((↑(ofAdd (-1 : ℤ)) : ℤₘ₀) ^ (-a)) ^ n = ofAdd (n : ℤ) ^ a := by
  rw [ofAdd_zpow (-1)]
  simp only [zpow_neg, zpow_one, inv_zpow', inv_inv, coe_zpow]
  rw [← zpow_natCast, ofAdd_zpow_zpow_comm, ← ofAdd_zpow]

-- Q: where?
instance : Nontrivial ℤₘ₀ˣ := (unitsWithZeroEquiv).toEquiv.nontrivial

-- [Mathlib.SetTheory.Cardinal.Basic, Mathlib.Data.ENat.Basic, Mathlib.Algebra.Order.Nonneg.Field,
--Mathlib.Algebra.Order.Ring.Cast, Mathlib.Data.NNRat.Defs, Mathlib.Algebra.Order.Ring.Abs]
theorem one_lt_zpow {α : Type _} [LinearOrderedCommGroupWithZero α] {a : α} (ha : 1 < a) {k : ℤ}
    (hk : 0 < k) : 1 < a ^ k := by
  lift k to ℕ using Int.le_of_lt hk
  rw [zpow_natCast]
  exact one_lt_pow' ha (Int.natCast_pos.mp hk).ne'

-- [Mathlib.Algebra.Order.GroupWithZero.Canonical]
theorem mul_lt_mul_right₀ {α : Type*} {a b c : α} [LinearOrderedCommGroupWithZero α]
    (hc : 0 < c) : a * c < b * c ↔ a < b := by
  rw [mul_comm a, mul_comm b]
  exact ⟨fun h ↦ lt_of_mul_lt_mul_of_le₀ h hc (le_refl _),
    fun h ↦ mul_lt_mul_of_lt_of_le₀ (le_refl _) (ne_of_gt hc) h⟩

--[Mathlib.Algebra.Order.GroupWithZero.Canonical]
-- *FAE* The lemma below was used only once and was basically already in mathlib: removed
-- theorem lt_mul_left₀ {α : Type _} {b c : α} [LinearOrderedCommGroupWithZero α] {a : α} (h : b < c)
--     (ha : a ≠ 0) : a * b < a * c := by simpa only [mul_comm a _] using mul_lt_right₀ a h ha

--[Mathlib.Algebra.Order.GroupWithZero.Canonical]
theorem one_lt_div' {α : Type _} [LinearOrderedCommGroupWithZero α] (a : α) {b : α} (hb : b ≠ 0) :
    1 < a / b ↔ b < a := by
  rw [← mul_lt_mul_right₀ (zero_lt_iff.mpr hb), one_mul, div_eq_mul_inv, inv_mul_cancel_right₀ hb]

--open scoped DiscreteValuation

theorem strictMonoOn_zpow {n : ℤ} (hn : 0 < n) : StrictMonoOn (fun x : ℤₘ₀ ↦ x ^ n) (Set.Ioi 0) :=
  fun a ha b _ hab ↦ by
    have ha0 : a ≠ 0 := ne_of_gt ha
    have han : a ^ n ≠ 0 := by
      rw [WithZero.ne_zero_iff_exists] at ha0 ⊢
      obtain ⟨x, hx⟩ := ha0
      exact ⟨x ^ n, by rw [← hx, WithZero.coe_zpow]⟩
    simp only [← one_lt_div' (b^n) han, ← div_zpow]
    exact one_lt_zpow ((one_lt_div' _ ha0).mpr hab) hn


-- [Mathlib.Data.Int.Lemmas, Mathlib.Data.ZMod.Defs, Mathlib.Algebra.Order.Field.Basic,
-- Mathlib.Data.NNRat.Defs, Mathlib.Algebra.Order.BigOperators.Group.Finset, Mathlib.Algebra.Order.Module.Pointwise]
theorem zpow_left_injOn {n : ℤ} (hn : n ≠ 0) : Set.InjOn (fun _x : ℤₘ₀ ↦ _x ^ n) (Set.Ioi 0) := by
  rcases hn.symm.lt_or_lt with h | h
  · exact (strictMonoOn_zpow h).injOn
  · refine fun a ha b hb (hab : a ^ n = b ^ n) ↦ (strictMonoOn_zpow (neg_pos.mpr h)).injOn ha hb ?_
    simp only [zpow_neg, zpow_neg, hab]

theorem zpow_left_inj {n : ℤ} {a b : ℤₘ₀} (ha : a ≠ 0) (hb : b ≠ 0) (hn : n ≠ 0) :
    a ^ n = b ^ n ↔ a = b :=
  Set.InjOn.eq_iff (zpow_left_injOn hn) (Set.mem_Ioi.mpr (zero_lt_iff.mpr ha))
    (Set.mem_Ioi.mpr (zero_lt_iff.mpr hb))

-- [Mathlib.Algebra.Order.Ring.Cast, Mathlib.Data.NNRat.Defs, Mathlib.Algebra.Order.Ring.Abs]
theorem ofAdd_neg_nat (n : ℕ) : (↑(ofAdd (-n : ℤ)) : ℤₘ₀) = ofAdd (-1 : ℤ) ^ n := by
  simp only [ofAdd_neg, coe_inv, inv_pow, coe_pow, inv_inj]
  rw [← @WithZero.coe_pow, WithZero.coe_inj, ← one_mul (n : ℤ), Int.ofAdd_mul, zpow_natCast]

theorem ofAdd_neg_one_lt_one : (↑(Multiplicative.ofAdd (-1 : ℤ)) : ℤₘ₀) < (1 : ℤₘ₀) := by
  rw [← WithZero.coe_one, WithZero.coe_lt_coe, ← ofAdd_zero, ofAdd_lt]
  exact neg_one_lt_zero

-- [Mathlib.Algebra.Order.Ring.Cast, Mathlib.Data.NNRat.Defs, Mathlib.Algebra.Order.Ring.Abs]
theorem lt_succ_iff_le (x : ℤₘ₀) (m : ℤ) :
    x < (↑(ofAdd (m + 1)) : ℤₘ₀) ↔ x ≤ (↑(ofAdd m) : ℤₘ₀) := by
  by_cases hx : x = 0
  · simpa only [hx, zero_le', iff_true_iff, zero_lt_iff] using WithZero.coe_ne_zero
  · obtain ⟨γ, rfl⟩ := WithZero.ne_zero_iff_exists.mp hx
    rw [coe_le_coe, coe_lt_coe, ← toAdd_le, ← toAdd_lt, toAdd_ofAdd, toAdd_ofAdd]
    exact ⟨Int.le_of_lt_add_one, Int.lt_add_one_of_le⟩

end WithZero


open WithZero

-- From this line, in PR #15741

/-- Given a nonzero `e : ℝ≥0`, this is the map `ℤₘ₀ → ℝ≥0` sending `0 ↦ 0` and
  `x ↦ e^(Multiplicative.toAdd (WithZero.unzero hx)` when `x ≠ 0` as a `MonoidWithZeroHom`. -/
def withZeroMultIntToNNReal {e : NNReal} (he : e ≠ 0) : ℤₘ₀ →*₀ ℝ≥0 where
  toFun := fun x ↦ if hx : x = 0 then 0 else e ^ Multiplicative.toAdd (WithZero.unzero hx)
  map_zero' := rfl
  map_one' := by
    simp only [dif_neg one_ne_zero]
    erw [toAdd_one, zpow_zero]
  map_mul' x y := by
    simp only
    by_cases hxy : x * y = 0
    · cases' zero_eq_mul.mp (Eq.symm hxy) with hx hy
      --either x = 0 or y = 0
      · rw [dif_pos hxy, dif_pos hx, MulZeroClass.zero_mul]
      · rw [dif_pos hxy, dif_pos hy, MulZeroClass.mul_zero]
    · cases' mul_ne_zero_iff.mp hxy with hx hy
      --  x ≠ 0 and y ≠ 0
      rw [dif_neg hxy, dif_neg hx, dif_neg hy, ← zpow_add' (Or.inl he), ← toAdd_mul]
      congr
      rw [← WithZero.coe_inj, WithZero.coe_mul, coe_unzero hx, coe_unzero hy, coe_unzero hxy]

theorem withZeroMultIntToNNReal_pos_apply {e : NNReal} (he : e ≠ 0) {x : ℤₘ₀} (hx : x = 0) :
    withZeroMultIntToNNReal he x = 0 := by
  simp only [withZeroMultIntToNNReal, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk]
  split_ifs; rfl

theorem withZeroMultIntToNNReal_neg_apply {e : NNReal} (he : e ≠ 0) {x : ℤₘ₀} (hx : x ≠ 0) :
    withZeroMultIntToNNReal he x = e ^ Multiplicative.toAdd (WithZero.unzero hx) := by
  simp only [withZeroMultIntToNNReal, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk]
  split_ifs; tauto; rfl

/-- `withZeroMultIntToNNReal` sends nonzero elements to nonzero elements. -/
theorem withZeroMultIntToNNReal_ne_zero {e : NNReal} {m : ℤₘ₀} (he : e ≠ 0) (hm : m ≠ 0) :
    withZeroMultIntToNNReal he m ≠ 0 := by
  simp only [ne_eq, map_eq_zero, hm, not_false_eq_true]

/-- `withZeroMultIntToNNReal` sends nonzero elements to positive elements. -/
theorem withZeroMultIntToNNReal_pos {e : NNReal} {m : ℤₘ₀} (he : e ≠ 0) (hm : m ≠ 0) :
    0 < withZeroMultIntToNNReal he m :=
  lt_of_le_of_ne zero_le' (withZeroMultIntToNNReal_ne_zero he hm).symm

-- [Mathlib.Data.NNReal.Basic]
/-- The map `withZeroMultIntToNNReal` is strictly monotone whenever `1 < e`. -/
theorem withZeroMultIntToNNReal_strictMono {e : NNReal} (he : 1 < e) :
    StrictMono (withZeroMultIntToNNReal (ne_zero_of_lt he)) := by
  intro x y hxy
  simp only [withZeroMultIntToNNReal, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk]
  split_ifs with hx hy hy
  · simp only [hy, not_lt_zero'] at hxy
  · exact NNReal.zpow_pos (ne_zero_of_lt he) _
  · simp only [hy, not_lt_zero'] at hxy
  · rw [zpow_lt_iff_lt he, Multiplicative.toAdd_lt, ← WithZero.coe_lt_coe, WithZero.coe_unzero hx,
      WithZero.coe_unzero hy]
    exact hxy

theorem eq_one {e : NNReal} {m : ℤₘ₀} (he0 : e ≠ 0) (he1 : e ≠ 1) (hm : m ≠ 0) : withZeroMultIntToNNReal he0 m = 1 ↔ m = 1 := by
  constructor
  · rw [withZeroMultIntToNNReal_neg_apply he0 hm]

    intro h
    convert_to toAdd (unzero hm) = 0
    simp only [toAdd_eq_zero]
    constructor
    intro a
    subst a
    simp_all only [ne_eq, unzero_coe]
    simp_all only [ne_eq, one_ne_zero, not_false_eq_true]
    rfl
    intro h
    rw [WithZero.unzero_coe (x:=m) _] at h


    have : 1 = e ^ 0 := by exact rfl
    rw [this] at h
    rw [zpow_inj (n:=0) _ he1] at h

    --rw [pow_eq_one_iff_cases] at h
    have : toAdd (unzero hm) = 0 := by

      sorry
    sorry
  · intro a
    subst a
    simp_all only [ne_eq, one_ne_zero, not_false_eq_true, map_one]



theorem foo {e : NNReal} {m : ℤₘ₀} (he : 1 < e) (hm : m ≠ 0) : withZeroMultIntToNNReal (ne_zero_of_lt he) m ≤ 1 ↔ m ≤ 1 := by
  constructor
  · intro h

    sorry
  · sorry
