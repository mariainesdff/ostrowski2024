import Mathlib.Analysis.Normed.Ring.Seminorm
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace MulRingNorm

/-- Two multiplicative ring norms `f, g` on `R` are equivalent if there exists a positive constant
  `c` such that for all `x ∈ R`, `(f x)^c = g x`.
  This could be generalised to ring_norm, but MulRingNorm does not extend this. -/
def equiv {R : Type*} [Ring R] (f : MulRingNorm R) (g : MulRingNorm R) :=
  ∃ c : ℝ, 0 < c ∧ (λ x : R => (f x) ^ c) = g

lemma equiv_refl {R : Type*} [Ring R] (f : MulRingNorm R) :
  equiv f f := by refine ⟨1, by linarith, by simp only [Real.rpow_one]⟩

lemma equiv_symm {R : Type*} [Ring R] (f g : MulRingNorm R) (hfg : equiv f g) :
    equiv g f :=
  sorry
/- begin
  rcases hfg with ⟨c, hfg1, hfg2⟩,
  refine ⟨1 / c, by simp only [hfg1, one_div, inv_pos], _⟩,
  rw ← hfg2,
  ext,
  simp only [one_div],
  have h1 : c ≠ 0 := by linarith,
  rw ← real.rpow_mul (map_nonneg f x),
  simp only [h1, mul_inv_cancel, ne.def, not_false_iff, real.rpow_one],
end -/

lemma equiv_trans {R : Type*} [ring R] (f g k : MulRingNorm R) (hfg : equiv f g) (hgk : equiv g k) :
  equiv f k :=
begin
  rcases hfg with ⟨c, hfg1, hfg2⟩,
  rcases hgk with ⟨d, hgk1, hgk2⟩,
  refine ⟨c * d, by simp only [hfg1, hgk1, zero_lt_mul_right], _⟩,
  rw ← hgk2,
  rw ← hfg2,
  ext,
  exact real.rpow_mul (map_nonneg f x) c d,
end

end MulRingNorm
