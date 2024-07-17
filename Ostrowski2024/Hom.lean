import Mathlib.RingTheory.Valuation.Basic
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

open scoped DiscreteValuation

open Multiplicative DiscreteValuation

@[elab_as_elim]
protected lemma Zm0.induction_on {motive : ℤₘ₀ → Prop} (zero : motive 0)
  (of_int : ∀ z : ℤ, motive (ofAdd z : Multiplicative ℤ)) (x : ℤₘ₀) : motive x :=
WithZero.recZeroCoe zero of_int x

noncomputable def Zm0.toFun (r : ℝ) (x : ℤₘ₀) : ℝ := WithZero.recZeroCoe 0 (fun z : Multiplicative ℤ ↦ r ^ (toAdd z)) x

variable (r : ℝ)

lemma Zm0.toFun_zero :Zm0.toFun r 0 = 0 := rfl

lemma Zm0.toFun_coe_int (z : ℤ) :Zm0.toFun r (ofAdd z : Multiplicative ℤ) = r ^ z := rfl

lemma Zm0.toFun_coe_mult_int (z : Multiplicative ℤ) :Zm0.toFun r z = r ^ (toAdd z) := rfl

lemma Zm0.toFun_zero_iff (a : ℤₘ₀) : Zm0.toFun r a = 0 ↔ a = 0 := by
  constructor
  · intro h
    simp only at h
    by_contra ha
    unfold toFun at h
    unfold WithZero.recZeroCoe at h
    simp only at h
    simp only at ha
    sorry
  · intro h
    rw [h]
    exact rfl
noncomputable def Zm0.toReal (r : ℝ) (h1: 0 < r) : ℤₘ₀ →* ℝ where
  toFun := Zm0.toFun r
  map_one' := by
    suffices toFun r 1 = r ^ 0 by
      convert this
    exact Zm0.toFun_coe_int r 0
  map_mul' := by
    intro x y
    simp only
    induction' x using Zm0.induction_on with x
    · simp only [Zm0.toFun_zero, zero_mul]
    · induction' y using Zm0.induction_on with y
      · simp only [Zm0.toFun_zero, mul_zero]
      · norm_cast
        simp only [toFun_coe_mult_int, toAdd_mul, toAdd_ofAdd]
        have h2: r ^ ((x : ℝ) + (y : ℝ)) = r ^ x * r ^ y := by
          rw [Real.rpow_add h1 x y]
          simp only [Real.rpow_intCast]
        rw [← h2]
        norm_cast
