import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.Analysis.Normed.Ring.Seminorm
import Ostrowski2024.Rationals
import Mathlib.Topology.Algebra.Valued.NormedValued
import Mathlib.RingTheory.Valuation.RankOne
import Ostrowski2024.Hom

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

variable (K : Type*) [Field K] [nf : NumberField K] (f : MulRingNorm K) (K' : Type*) [Field K']
[Algebra K' K]

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

lemma restr_def (x : K') : (mulRingNorm_restriction K f K') x = f (x • (1 : K)) := rfl

lemma bdd_restr_Q : (∀ n : ℕ, f n ≤ 1) ↔  (∀ n : ℕ, (mulRingNorm_restriction K f ℚ) n ≤ 1) := by
  constructor
  all_goals intro hn n
  all_goals specialize hn n
  · simp only [restr_def, Rat.smul_one_eq_cast, Rat.cast_natCast, hn]
  · rw [restr_def] at hn
    simp only [Rat.smul_one_eq_cast, Rat.cast_natCast] at hn
    exact hn

section Archimedean

variable (notbdd : ¬ ∀ n : ℕ, f n ≤ 1)

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

lemma restr_to_Q_real : MulRingNorm.equiv (mulRingNorm_restriction K f ℚ) Rational.mulRingNorm_real := by
  apply Rational.mulRingNorm_equiv_standard_of_unbounded
  intro h
  rw [← bdd_restr_Q] at h
  exact notbdd h

theorem ostr_arch :
    ∃ φ : K →+* ℂ, MulRingNorm.equiv f (mulRingNorm_arch K φ) := by
  rcases restr_to_Q_real K f notbdd with ⟨c, hc1, hc2⟩
  unfold MulRingNorm.equiv
  rw [exists_comm]
  use c
  rw [exists_and_left]
  refine ⟨hc1, ?_⟩
  sorry

end Archimedean

section Nonarchimedean

variable (P : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))

/- def foo  :
    Valuation.RankOne (R:=K) (IsDedekindDomain.HeightOneSpectrum.valuation P) :=
{ hom:= {
  toFun := sorry
  map_zero' := sorry
  map_one' := sorry
  map_mul' := sorry
}
  strictMono':= sorry
  nontrivial':= sorry
} -/

noncomputable def mulRingNorm_Padic : MulRingNorm K :=
{ toFun     := fun x : K ↦ (Zm0.toReal) 2 (zero_lt_two) ((IsDedekindDomain.HeightOneSpectrum.valuation P) x)
--2 ^ ( ((IsDedekindDomain.HeightOneSpectrum.valuation P) x))
--(((foo K P).hom ((IsDedekindDomain.HeightOneSpectrum.valuation P) x)) : ℝ)
--(hom ((IsDedekindDomain.HeightOneSpectrum.valuation v) x) : ℝ) --λ x : K => (padicNorm p x : ℝ),
  map_zero' := by simp only [map_zero]; exact rfl
  add_le'   := by simp only; sorry
  neg'      := by simp only [Valuation.map_neg, implies_true]
  eq_zero_of_map_eq_zero' := by
    simp only
    intro x hx
    sorry
  map_one' := by simp only [map_one]
  map_mul' := by simp only [map_mul, implies_true]
}
end Nonarchimedean
