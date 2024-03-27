import Mathlib.Analysis.Normed.Ring.Seminorm
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace MulRingNorm

/-- Two multiplicative ring norms `f, g` on `R` are equivalent if there exists a positive constant
  `c` such that for all `x ∈ R`, `(f x)^c = g x`.
  This could be generalised to RingNorm, but MulRingNorm does not extend this. -/
def equiv {R : Type*} [Ring R] (f : MulRingNorm R) (g : MulRingNorm R) :=
  ∃ c : ℝ, 0 < c ∧ (λ x : R => (f x) ^ c) = g

lemma equiv_refl {R : Type*} [Ring R] (f : MulRingNorm R) : equiv f f := by
  refine ⟨1, by linarith, by simp only [Real.rpow_one]⟩

lemma equiv_symm {R : Type*} [Ring R] (f g : MulRingNorm R) (hfg : equiv f g) : equiv g f := by
  rcases hfg with ⟨c, hcpos, h⟩
  use 1/c
  constructor
  · simp only [one_div, inv_pos, hcpos]
  · replace h := congr_fun h
    ext x
    rw [← h x]
    simp only [AddGroupSeminorm.toFun_eq_coe, MulRingSeminorm.toFun_eq_coe, one_div, map_nonneg]
    exact Real.rpow_rpow_inv (apply_nonneg f x) (ne_of_lt hcpos).symm

lemma equiv_trans {R : Type*} [Ring R] (f g k : MulRingNorm R) (hfg : equiv f g) (hgk : equiv g k) :
    equiv f k := by
  rcases hfg with ⟨c, hcPos, hfg⟩
  rcases hgk with ⟨d, hdPos, hgk⟩
  refine ⟨c*d, (mul_pos_iff_of_pos_left hcPos).mpr hdPos, ?_⟩
  ext x
  rw [Real.rpow_mul (apply_nonneg f x), congr_fun hfg x, congr_fun hgk x]

end MulRingNorm

lemma MulRingNorm_nat_le_nat (n : ℕ) (f : MulRingNorm ℚ) : f n ≤ n := by
  induction' n with n hn
  · simp only [Nat.zero_eq, CharP.cast_eq_zero, map_zero, le_refl]
  · simp only [Nat.cast_succ]
    calc
      f (↑n + 1) ≤ f (↑n) + f 1 := f.add_le' ↑n 1
      _ = f (↑n) + 1 := by rw [map_one]
      _ ≤ ↑n + 1 := add_le_add_right hn 1
