
import Ostrowski2024.Basic
import Ostrowski2024.MulRingNormRat
import Mathlib.Analysis.SpecialFunctions.Log.Base


/-!
# Ostrowski's theorem for ℚ

## References
* https://kconrad.math.uconn.edu/blurbs/gradnumthy/ostrowskiQ.pdf
* https://kconrad.math.uconn.edu/blurbs/gradnumthy/ostrowskinumbfield.pdf

## Tags
ring_norm, ostrowski
-/

set_option autoImplicit false

/-!
Throughout this file, `f` is an arbitrary absolute value.
-/
variable {f : MulRingNorm ℚ}

noncomputable section

namespace Rational

section Real

/-- The usual absolute value on ℚ. -/
def mulRingNorm_real : MulRingNorm ℚ :=
{ toFun    := λ x : ℚ => |x|
  map_zero' := by simp only [Rat.cast_zero, abs_zero]
  add_le'   := norm_add_le
  neg'      := norm_neg
  eq_zero_of_map_eq_zero' := by simp only [abs_eq_zero, Rat.cast_eq_zero, imp_self, forall_const]
  map_one' := by simp only [Rat.cast_one, abs_one]
  map_mul' := by
    simp only [Rat.cast_mul]
    exact_mod_cast abs_mul
}

@[simp] lemma mul_ring_norm_eq_abs (r : ℚ) : mulRingNorm_real r = |r| := by
  simp only [Rat.cast_abs]
  rfl

end Real

section Padic

/-- The p-adic norm on ℚ. -/
def mulRingNorm_padic (p : ℕ) [hp : Fact (Nat.Prime p)] : MulRingNorm ℚ :=
{ toFun     := λ x : ℚ => (padicNorm p x : ℝ),
  map_zero' := by simp only [padicNorm.zero, Rat.cast_zero]
  add_le'   := by simp only; norm_cast; exact fun r s => padicNorm.triangle_ineq r s
  neg'      := by simp only [eq_self_iff_true, forall_const, padicNorm.neg];
  eq_zero_of_map_eq_zero' := by simp only [Rat.cast_eq_zero]; apply padicNorm.zero_of_padicNorm_eq_zero
  map_one' := by simp only [ne_eq, one_ne_zero, not_false_eq_true, padicNorm.eq_zpow_of_nonzero,
    padicValRat.one, neg_zero, zpow_zero, Rat.cast_one]
  map_mul' := by simp only [padicNorm.mul, Rat.cast_mul, forall_const]
}

@[simp] lemma mul_ring_norm_eq_padic_norm (p : ℕ) [Fact (Nat.Prime p)] (r : ℚ) :
  mulRingNorm_padic p r = padicNorm p r := rfl

lemma mul_ring_norm.padic_is_nonarchimedean (p : ℕ) [hp : Fact (Nat.Prime p)] (a b : ℚ) :
    mulRingNorm_padic p (a + b) ≤ max (mulRingNorm_padic p a) (mulRingNorm_padic p b) := by
  rw [mul_ring_norm_eq_padic_norm]
  rw [mul_ring_norm_eq_padic_norm]
  rw [mul_ring_norm_eq_padic_norm]
  norm_cast
  exact padicNorm.nonarchimedean
  done

end Padic

section Archimedean

-- ## step 1
-- if |n|>1 for some n then |n|>1 for *all* n \geq 2 (by proving contrapositive)

-- auxilia

lemma notbdd_implies_all_gt_one (notbdd: ¬ ∀(n : ℕ), f n ≤ 1) : ∀(n : ℕ) (hn: 1 < n), f n > 1 := by
  contrapose! notbdd
  rcases notbdd with ⟨n0, hn0_ge2, hfn0⟩
  have hnk {k n : ℕ} (hk : 0 < k) (hn : 1 < n) : (f n)^k ≤ (n0 * ((k * Real.log n) / (Real.log n0) + 1)) := by
    set L := Nat.digits n0 (n^k)
    set d := L.length - 1 with hd
    have hd_natlog : d = Nat.log n0 (n^k) := by
      rw [hd, Nat.digits_len _ _ hn0_ge2 (pow_ne_zero k (ne_zero_of_lt hn)), Nat.add_sub_cancel]
    have hd_log : d ≤ Real.logb n0 (n^k) := by
      rw [hd_natlog, show (Nat.log n0 (n^k) : ℝ) = ((Nat.log n0 (n^k) : ℤ) : ℝ) by rfl, ← @Int.log_natCast ℚ, ← Real.floor_logb_nat_cast]
      -- Real.floor_logb_nat_cast



  sorry



-- ## step 2
-- given m,n \geq 2 and |m|=m^s, |n|=n^t for s,t >0, prove t \leq s

lemma compare_exponents (m n : ℕ) (s t : ℝ) (hs : s > 0) (ht : t > 0) (hmge : m ≥ 2) (hnge : n ≥ 2) (hm : f m = m ^ s) (hn : f n = n ^ t) : t ≤ s := sorry


-- ## final step
-- finish the proof by symmetry (exchanging m,n and proving s \leq t) TODO

-- ## Archimedean case: end goal
/--
   If `f` is not bounded and not trivial, then it is equivalent to the usual absolute value on ℚ.
-/
theorem notbdd_implies_equiv_real (notbdd: ¬ ∀(n : ℕ), f n ≤ 1) (hf_nontriv : f ≠ 1)  : MulRingNorm.equiv f mulRingNorm_real := sorry

end Archimedean

section Nonarchimedean


-- ## Non-archimedean case: end goal
/--
  If `f` is bounded and not trivial, then it is equivalent to a p-adic absolute value.
-/
theorem bdd_implies_equiv_padic (bdd: ∀ n : ℕ, f n ≤ 1) (hf_nontriv : f ≠ 1) :
∃ p, ∃ (hp : Fact (Nat.Prime p)), MulRingNorm.equiv f (mulRingNorm_padic p) :=
  by sorry

end Nonarchimedean

/-- Ostrowski's Theorem -/
theorem ringNorm_padic_or_real (f : MulRingNorm ℚ) (hf_nontriv : f ≠ 1) :
    (MulRingNorm.equiv f mulRingNorm_real) ∨
    ∃ (p : ℕ) (hp : Fact (Nat.Prime p)), MulRingNorm.equiv f (@mulRingNorm_padic p hp) := by
  by_cases bdd : ∀ n : ℕ, f n ≤ 1
  · right
    apply bdd_implies_equiv_padic bdd hf_nontriv
  · left
    apply notbdd_implies_equiv_real bdd hf_nontriv
end Rational
