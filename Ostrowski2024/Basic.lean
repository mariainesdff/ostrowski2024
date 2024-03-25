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
    equiv g f := by
-- this proof looks terrible, I know.
    rcases hfg with ⟨c,hcpos,h⟩
    use 1/c
    constructor
    · simp only [one_div, inv_pos, hcpos]
    · have := congr_fun h
      ext x
      specialize this x
      rw [← this]
      simp only [AddGroupSeminorm.toFun_eq_coe, MulRingSeminorm.toFun_eq_coe, one_div, map_nonneg]
      have (x c : ℝ) (hx : 0 ≤ x) (h : 0 < c) : (x^c)^(c⁻¹) = x := by
        refine Real.rpow_rpow_inv ?hx ?hy
        exact hx
        linarith
      apply this
      exact apply_nonneg f x
      exact hcpos
    done

lemma equiv_trans {R : Type*} [Ring R] (f g k : MulRingNorm R) (hfg : equiv f g) (hgk : equiv g k) :
  equiv f k := by
  rcases hfg with ⟨c, hcPos, hfg⟩
  rcases hgk with ⟨d, hdPos, hgk⟩
  use c * d
  constructor
  simp only [gt_iff_lt, hcPos, mul_pos_iff_of_pos_left, hdPos]
  ext x
  replace hfg := congr_fun hfg x
  replace hgk := congr_fun hgk x
  rw [Real.rpow_mul (apply_nonneg f x),hfg,hgk]

end MulRingNorm