
--import Ostrowski2024.Basic
import Ostrowski2024.MulRingNormRat
--import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
--import Mathlib.Analysis.SpecialFunctions.Pow.Real
-- import Mathlib.Algebra.Order.Monoid.Lemmas
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Data.Set.Finite


/-!
# Ostrowski's theorem for ℚ

## References
* https://kconrad.math.uconn.edu/blurbs/gradnumthy/ostrowskiQ.pdf
* https://kconrad.math.uconn.edu/blurbs/gradnumthy/ostrowskinumbfield.pdf

## Tags
ring_norm, ostrowski
-/

--set_option autoImplicit false

/-!
Throughout this file, `f` is an arbitrary absolute value.
-/
variable {f : MulRingNorm ℚ}

noncomputable section

namespace Rational

section Real

/-- The usual absolute value on ℚ. -/
def mulRingNorm_real : MulRingNorm ℚ :=
{ toFun    := fun x : ℚ ↦ |x|
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

end Padic

section Archimedean

-- ## auxiliary Lemmas for lists

-- add to Mathlib.Analysis.Normed.Ring.Seminorm

/-- Triangle inequality for mulRingNorm applied to a List. -/
lemma mulRingNorm_sum_le_sum_mulRingNorm {R : Type*} [NonAssocRing R] (l : List R)
    (f : MulRingNorm R) : f l.sum ≤ (l.map f).sum := by
  induction l with
  | nil => simp only [List.sum_nil, map_zero, List.map_nil, le_refl]
  | cons head tail ih =>
    simp only [List.sum_cons, List.map_cons]
    calc f (head + List.sum tail) ≤ f head + f (List.sum tail) := by apply f.add_le'
      _ ≤ f head + List.sum (List.map f tail) := by simp only [add_le_add_iff_left, ih]

/-- Given an two integers `n, m` with `m > 1` the mulRingNorm of `n` is bounded by
    `m + m * f m + m * (f m) ^ 2 + ... + m * (f m) ^ d` where `d` is the number of digits of the
    expansion of `n` in base `m`. -/
lemma MulRingNorm_n_le_sum_digits (n : ℕ) {m : ℕ} (hm : 1 < m):
    f n ≤ ((Nat.digits m n).mapIdx fun i _ ↦ m * (f m) ^ i).sum := by
  set L := Nat.digits m n
  set L' : List ℚ := List.map Nat.cast (L.mapIdx fun i a ↦ (a * m ^ i)) with hL'
  -- If `c` is a digit in the expansion of `n` in base `m`, then `f c` is less than `m`.
  have hcoef {c : ℕ} (hc : c ∈ Nat.digits m n) : f c < m :=
    lt_of_le_of_lt (MulRingNorm_nat_le_nat c f) (mod_cast Nat.digits_lt_base hm hc)
  calc
  f n = f ((Nat.ofDigits m L : ℕ) : ℚ) := by rw [Nat.ofDigits_digits m n]
    _ = f (L'.sum) := by rw [Nat.ofDigits_eq_sum_mapIdx]; norm_cast
    _ ≤ (L'.map f).sum := mulRingNorm_sum_le_sum_mulRingNorm L' f
    _ ≤ (L.mapIdx fun i _ ↦ m * (f m) ^ i).sum := by
      simp only [hL', List.mapIdx_eq_enum_map, List.map_map]
      apply List.sum_le_sum
      rintro ⟨i,a⟩ hia
      dsimp [Function.uncurry]
      replace hia := List.mem_enumFrom hia
      push_cast
      rw [map_mul, map_pow]
      apply mul_le_mul_of_nonneg_right (le_of_lt (hcoef _))
        (pow_nonneg (apply_nonneg f ↑m) i)
      simp only [zero_le, zero_add, tsub_zero, true_and] at hia
      refine List.mem_iff_get.mpr ?_
      use ⟨i, hia.1⟩
      exact id (Eq.symm hia.2)

/- ## Auxiliary lemma for limits-/

open Filter

/- If `a : ℝ` is bounded above by a function `g : ℕ → ℝ` for every `0 < k` then it is less or
equal than the limit `lim_{k → ∞} g(k)`-/
private lemma le_of_limit_le {a : ℝ} {g : ℕ → ℝ} {l : ℝ} (ha : ∀ (k : ℕ) (_ : 0 < k), a ≤ g k)
  (hg : Tendsto g Filter.atTop (nhds l)) : a ≤ l := by
  apply le_of_tendsto_of_tendsto tendsto_const_nhds hg
  rw [EventuallyLE, eventually_atTop]
  exact ⟨1, ha⟩


/- For any `C > 0`, the limit of `C ^ (1/k)` is 1 as `k → ∞`. -/
private lemma tendsto_root_atTop_nhds_one {C : ℝ} (hC : 0 < C) : Tendsto
    (fun k : ℕ ↦ C ^ (k : ℝ)⁻¹) atTop (nhds 1) := by
  convert_to Tendsto ((fun k ↦ C ^ k) ∘ (fun k : ℝ ↦ k⁻¹) ∘ (Nat.cast))
    atTop (nhds 1)
  exact Tendsto.comp (Continuous.tendsto' (continuous_iff_continuousAt.2
    (fun a ↦ Real.continuousAt_const_rpow (Ne.symm (ne_of_lt hC)))) 0 1 (Real.rpow_zero C))
    <| Tendsto.comp tendsto_inv_atTop_zero tendsto_natCast_atTop_atTop

/-extends the lemma `tendsto_rpow_div` when the function has natural input-/
private lemma tendsto_nat_rpow_div : Tendsto (fun k : ℕ ↦ (k : ℝ) ^ (k : ℝ)⁻¹)
    atTop (nhds 1) := by
  convert_to Tendsto ((fun k : ℝ ↦ k ^ k⁻¹) ∘ (Nat.cast) ) atTop (nhds 1)
  apply Tendsto.comp _ tendsto_natCast_atTop_atTop
  simp_rw [← one_div]
  exact tendsto_rpow_div

open Real Nat

-- ## step 1

/-- If `f n > 1` for some `n` then `f n > 1` for all `n ≥ 2`.-/
lemma one_lt_of_not_bounded (notbdd : ¬ ∀ (n : ℕ), f n ≤ 1) {n₀ : ℕ} (hn₀ : 1 < n₀) : 1 < f n₀ := by
  contrapose! notbdd with h
  --rcases h with ⟨hn₀, hfn₀⟩
  intro n
  have h_ineq1 {m : ℕ} (hm : 1 ≤ m) : f m ≤ n₀ * (Real.logb n₀ m + 1) := by
    /- L is the string of digits of `n` in the base `n₀`-/
    set L := Nat.digits n₀ m
    calc
    f m ≤ (L.mapIdx fun i _ ↦ n₀ * (f n₀) ^ i).sum := MulRingNorm_n_le_sum_digits m hn₀
    _ ≤ (L.mapIdx fun _ _ ↦ (n₀ : ℝ)).sum := by
      simp only [List.mapIdx_eq_enum_map, List.map_map]
      apply List.sum_le_sum
      rintro ⟨i,a⟩ _
      simp only [Function.comp_apply, Function.uncurry_apply_pair]
      exact mul_le_of_le_of_le_one' (mod_cast le_refl n₀) (pow_le_one i (apply_nonneg f ↑n₀) h)
        (pow_nonneg (apply_nonneg f ↑n₀) i) (cast_nonneg n₀)
    _ ≤ n₀ * (Real.logb n₀ m + 1) := by
      rw [List.mapIdx_eq_enum_map, List.eq_replicate_of_mem (a:=(n₀ : ℝ))
        (l := List.map (Function.uncurry fun _ _ ↦ n₀) (List.enum L)),
        List.sum_replicate, List.length_map, List.enum_length, nsmul_eq_mul, mul_comm]
      · rw [Nat.digits_len n₀ m hn₀ (not_eq_zero_of_lt hm)]
        apply mul_le_mul_of_nonneg_left _ (cast_nonneg n₀)
        push_cast
        simp only [add_le_add_iff_right]
        exact natLog_le_logb m n₀
      · simp_all only [List.mem_map, Prod.exists, Function.uncurry_apply_pair, exists_and_right,
          and_imp, implies_true, forall_exists_index, forall_const]
  -- For h_ineq2 we need to exclude the case n = 0.
  rcases eq_or_ne n 0 with rfl | h₀; simp only [CharP.cast_eq_zero, map_zero, zero_le_one]
  -- h_ineq2 needs to be in this form because it is applied in le_of_limit_le above
  have h_ineq2 : ∀ (k : ℕ), 0 < k →
      f n ≤ (n₀ * (Real.logb n₀ n + 1)) ^ (k : ℝ)⁻¹ * k ^ (k : ℝ)⁻¹ := by
    intro k hk
    have h_exp : (f n ^ (k : ℝ)) ^ (k : ℝ)⁻¹ = f n := by
      apply Real.rpow_rpow_inv (apply_nonneg f ↑n)
      simp only [ne_eq, cast_eq_zero]
      exact Nat.pos_iff_ne_zero.mp hk
    rw [← Real.mul_rpow (mul_nonneg (cast_nonneg n₀) (add_nonneg (Real.logb_nonneg
      (one_lt_cast.mpr hn₀) (mod_cast Nat.one_le_of_lt (zero_lt_of_ne_zero h₀))) (zero_le_one' ℝ)))
      (cast_nonneg k), ← h_exp, Real.rpow_natCast, ← map_pow, ← cast_pow]
    gcongr
    apply le_trans (h_ineq1 (one_le_pow k n (zero_lt_of_ne_zero h₀)))
    rw [mul_assoc, cast_pow, Real.logb_pow (mod_cast zero_lt_of_ne_zero h₀), mul_comm _ (k : ℝ),
      mul_add (k : ℝ), mul_one]
    gcongr
    exact one_le_cast.mpr hk
-- For prod_limit below we need to exclude n = 1 also.
  rcases eq_or_ne n 1 with rfl | h₁; simp only [cast_one, map_one, le_refl]
  have prod_limit : Filter.Tendsto
      (fun k : ℕ ↦ (n₀ * (Real.logb n₀ n + 1)) ^ (k : ℝ)⁻¹ * (k ^ (k : ℝ)⁻¹))
      Filter.atTop (nhds 1) := by
    nth_rw 2 [← mul_one 1]
    have hnlim : Filter.Tendsto (fun k : ℕ ↦ (n₀ * (Real.logb n₀ n + 1)) ^ (k : ℝ)⁻¹)
        Filter.atTop (nhds 1) := tendsto_root_atTop_nhds_one
        (mul_pos (mod_cast (lt_trans zero_lt_one hn₀))
        (add_pos (Real.logb_pos (mod_cast hn₀) (by norm_cast; omega)) Real.zero_lt_one))
    exact Filter.Tendsto.mul hnlim tendsto_nat_rpow_div
  exact le_of_limit_le h_ineq2 prod_limit

-- ## step 2
-- given m,n \geq 2 and |m|=m^s, |n|=n^t for s,t >0, prove t \leq s

section Step2

/- Multiplication by a constant moves in a List.sum -/
private lemma list_mul_sum {R : Type*} [CommSemiring R] {T : Type*} (l : List T) (y : R) : ∀ x : R,
    List.sum (List.mapIdx (fun i _ => x * y ^ i) (l)) =
    x * List.sum (List.mapIdx (fun i _ => y ^ i) (l)) := by
  induction l with
  | nil => simp only [List.mapIdx_nil, List.sum_nil, mul_zero, forall_const]
  | cons head tail ih =>
    intro x
    simp_rw [List.mapIdx_cons, pow_zero, mul_one, List.sum_cons, mul_add, mul_one]
    have (a : ℕ) : y ^ (a + 1) = y * y ^ a := by ring
    simp_rw [this, ← mul_assoc, ih, ← mul_assoc]

/- Geometric sum for lists -/
private lemma list_geom {T : Type*} {F : Type*} [Field F] (l : List T) {y : F} (hy : y ≠ 1) :
    List.sum (List.mapIdx (fun i _ => y ^ i) l) = (y ^ l.length - 1) / (y - 1) := by
  induction l with
  | nil => simp only [List.mapIdx_nil, List.sum_nil, List.length_nil, pow_zero, sub_self, zero_div]
  | cons head tail ih =>
    simp only [List.mapIdx_cons, pow_zero, List.sum_cons, List.length_cons]
    have (a : ℕ ) : y ^ (a + 1) = y * y ^ a := by ring
    simp_rw [this, list_mul_sum, ih]
    simp only [mul_div, ← same_add_div (sub_ne_zero.2 hy), mul_sub, mul_one, sub_add_sub_cancel']

open Real

variable {m n : ℕ} (hm : 1 < m) (hn : 1 < n) (notbdd : ¬ ∀ (n : ℕ), f n ≤ 1)

include hm notbdd in
private lemma expr_pos : 0 < m * f m / (f m - 1) := by
  apply div_pos (mul_pos (mod_cast zero_lt_of_lt hm)
      (map_pos_of_ne_zero f (mod_cast ne_zero_of_lt hm)))
  linarith only [one_lt_of_not_bounded notbdd hm]

include hn hm notbdd in
private lemma param_upperbound (k : ℕ) (hk : k ≠ 0) :
    f n ≤ (m * f m / (f m - 1)) ^ (k : ℝ)⁻¹ * (f m) ^ (logb m n) := by
  have h_ineq1 {m n : ℕ} (hm : 1 < m) (hn : 1 < n) :
      f n ≤ (m * f m / (f m - 1)) * (f m) ^ (logb m n) := by
    let d := Nat.log m n
    calc
    f n ≤ ((Nat.digits m n).mapIdx fun i _ ↦ m * (f m) ^ i).sum :=
      MulRingNorm_n_le_sum_digits n hm
    _ = m * ((Nat.digits m n).mapIdx fun i _ ↦ (f m) ^ i).sum := list_mul_sum (m.digits n) (f m) m
    _ = m * ((f m ^ (d + 1) - 1) / (f m - 1)) := by
      rw [list_geom _ (ne_of_gt (one_lt_of_not_bounded notbdd hm)),
      (Nat.digits_len m n hm (not_eq_zero_of_lt hn)).symm]
    _ ≤ m * ((f m ^ (d + 1))/(f m - 1)) := by
      gcongr
      linarith only [one_lt_of_not_bounded notbdd hm]
      simp only [tsub_le_iff_right, le_add_iff_nonneg_right, zero_le_one]
    _ = ↑m * f ↑m / (f ↑m - 1) * f ↑m ^ d := by ring
    _ ≤ ↑m * f ↑m / (f ↑m - 1) * f ↑m ^ logb ↑m ↑n := by
      gcongr
      exact le_of_lt (expr_pos hm notbdd)
      rw [← Real.rpow_natCast, Real.rpow_le_rpow_left_iff (one_lt_of_not_bounded notbdd hm)]
      exact natLog_le_logb n m
  have h_ineq2 (k : ℕ) (hk : k ≠ 0) :
      (f n) ^ k ≤ (m * f m / (f m - 1)) * (f m) ^ (k * logb m n) := by
    calc
    (f n) ^ k = f ↑(n ^ k) := by simp only [cast_pow, map_pow]
    _ ≤ (m * f m / (f m - 1)) * (f m) ^ (logb m ↑(n ^ k)) := h_ineq1 hm (Nat.one_lt_pow hk hn)
    _ = (m * f m / (f m - 1)) * (f m) ^ (k * logb m n) := by
      rw [cast_pow, Real.logb_pow]
      exact_mod_cast zero_lt_of_lt hn
  apply le_of_pow_le_pow_left hk (mul_nonneg (rpow_nonneg
    (le_of_lt (expr_pos hm notbdd)) (k : ℝ)⁻¹) (rpow_nonneg (apply_nonneg f ↑m) (logb m n)))
  nth_rw 2 [← Real.rpow_natCast]
  rw [mul_rpow (rpow_nonneg (le_of_lt (expr_pos hm notbdd)) (k : ℝ)⁻¹)
    (rpow_nonneg (apply_nonneg f ↑m) (logb ↑m ↑n)), ← rpow_mul (le_of_lt (expr_pos hm notbdd)),
    ← rpow_mul (apply_nonneg f ↑m), inv_mul_cancel₀ (mod_cast hk), rpow_one, mul_comm (logb ↑m ↑n)]
  exact h_ineq2 k hk

include hm hn notbdd in
/-- Given two natural numbers `n, m` greater than 1 we have `f n ≤ f m ^ logb m n`. -/
lemma mulRingNorm_le_mulRingNorm_pow_log : f n ≤ f m ^ logb m n := by
  apply le_of_limit_le (g:=fun k ↦ (m * f m / (f m - 1)) ^ (k : ℝ)⁻¹ * (f m) ^ (logb m n))
  · intro k hk
    exact param_upperbound hm hn notbdd k (not_eq_zero_of_lt hk)
  · nth_rw 2 [← one_mul (f ↑m ^ logb ↑m ↑n)]
    exact Tendsto.mul_const _ (tendsto_root_atTop_nhds_one (expr_pos hm notbdd))

include hm hn notbdd in
private lemma le_exponents {s t : ℝ} (hfm : f m = m ^ s) (hfn : f n = n ^ t)  : t ≤ s := by
    have hmn : f n ≤ f m ^ Real.logb m n := mulRingNorm_le_mulRingNorm_pow_log hm hn notbdd
    rw [← Real.rpow_le_rpow_left_iff (x:=n) (mod_cast hn), ← hfn]
    apply le_trans hmn
    rw [hfm, ← Real.rpow_mul (cast_nonneg m), mul_comm, Real.rpow_mul (cast_nonneg m),
      Real.rpow_logb (mod_cast zero_lt_of_lt hm) (mod_cast Nat.ne_of_lt' hm)
      (mod_cast zero_lt_of_lt hn)]

include hm hn notbdd in
private lemma symmetric_roles {s t : ℝ} (hfm : f m = m ^ s) (hfn : f n = n ^ t) : s = t :=
  le_antisymm (le_exponents hn hm notbdd hfn hfm) (le_exponents hm hn notbdd hfm hfn)

-----
end Step2

-- ## final step
-- finish the proof by symmetry (exchanging m,n and proving s \leq t) TODO


-- ## Archimedean case: end goal
/-- If `f` is not bounded and not trivial, then it is equivalent to the standard absolute value on
`ℚ`. -/
theorem mulRingNorm_equiv_standard_of_unbounded (notbdd: ¬ ∀ (n : ℕ), f n ≤ 1) :
    MulRingNorm.equiv f mulRingNorm_real := by
  obtain ⟨m, hm⟩ := Classical.exists_not_of_not_forall notbdd
  have oneltm : 1 < m := by
    by_contra!
    apply hm
    replace this : m = 0 ∨ m = 1 := by omega
    rcases this with (rfl | rfl)
    all_goals simp only [CharP.cast_eq_zero, map_zero, zero_le_one,Nat.cast_one, map_one, le_refl]
  rw [← NormRat_equiv_iff_equiv_on_Nat]
  set s := Real.logb m (f m) with hs
  use s⁻¹
  refine ⟨inv_pos.2 (Real.logb_pos (Nat.one_lt_cast.2 oneltm)
    (one_lt_of_not_bounded notbdd oneltm)), ?_⟩
  intro n
  by_cases h1 : n ≤ 1
  · by_cases h2 : n = 1
    · simp only [h2, mul_ring_norm_eq_abs, abs_cast, Rat.cast_natCast, cast_one, map_one,
        Real.one_rpow]
    · have : n = 0 := by omega
      rw [this, hs]
      simp only [CharP.cast_eq_zero, map_zero]
      rw [Real.rpow_eq_zero le_rfl]
      simp only [ne_eq, inv_eq_zero, Real.logb_eq_zero, cast_eq_zero, cast_eq_one, map_eq_zero,
        not_or]
      push_neg
      exact ⟨not_eq_zero_of_lt oneltm, Nat.ne_of_lt' oneltm, mod_cast (fun a ↦ a),
        not_eq_zero_of_lt oneltm, ne_of_not_le hm, by linarith only [apply_nonneg f ↑m]⟩
  · simp only [mul_ring_norm_eq_abs, abs_cast, Rat.cast_natCast]
    rw [Real.rpow_inv_eq (apply_nonneg f ↑n) (cast_nonneg n)
      (Real.logb_ne_zero_of_pos_of_ne_one (one_lt_cast.mpr oneltm) (by linarith only [hm])
      (by linarith only [hm]))]
    simp only [not_le] at h1
    have hfm : f m = m ^ s := by rw [Real.rpow_logb (mod_cast zero_lt_of_lt oneltm)
      (mod_cast Nat.ne_of_lt' oneltm) (by linarith only [hm])]
    have hfn : f n = n ^ (Real.logb n (f n)) := by
      rw [Real.rpow_logb (mod_cast zero_lt_of_lt h1) (mod_cast Nat.ne_of_lt' h1)
      (by apply map_pos_of_ne_zero; exact_mod_cast not_eq_zero_of_lt h1)]
    rwa [← hs, symmetric_roles oneltm h1 notbdd hfm hfn]

end Archimedean

section Nonarchimedean

section step_1

-- ## Non-archimedean: step 1 define `p = smallest n s. t. 0 < |n| < 1`

variable (bdd: ∀ n : ℕ, f n ≤ 1)

include bdd in
 /-- There exists a minimal positive integer with absolute value smaller than 1 -/
lemma p_exists  (hf_nontriv : f ≠ 1) : ∃ (p : ℕ), (0 < f p ∧ f p < 1) ∧
    ∀ (m : ℕ), 0 < f m ∧ f m < 1 → p ≤ m := by
  have hn : ∃ (n : ℕ), n ≠ 0 ∧ f n ≠ 1 := by
  -- there is a positive integer with absolute value different from one
    by_contra h
    apply hf_nontriv
    push_neg at h
    apply NormRat_eq_iff_eq_on_Nat.1
    intro n
    by_cases hn0 : n=0
    · rw [hn0]
      simp only [CharP.cast_eq_zero, map_zero]
    · push_neg at hn0
      simp only [MulRingNorm.apply_one, Nat.cast_eq_zero, hn0, ↓reduceIte, h n hn0]
  obtain ⟨n,hn1,hn2⟩ := hn
  set P := {m : ℕ | 0 < f ↑m ∧ f ↑m < 1}
  have hPnonempty : Set.Nonempty P := by
    use n
    exact ⟨map_pos_of_ne_zero f (Nat.cast_ne_zero.mpr hn1), lt_of_le_of_ne (bdd n) hn2⟩
  use sInf P
  refine ⟨Nat.sInf_mem hPnonempty, ?_⟩
  intro m hm
  exact Nat.sInf_le hm

end step_1

section steps_2_3_4
-- ## Non-archimedean case: Step 2. p is prime

variable (bdd: ∀ n : ℕ, f n ≤ 1)  (p : ℕ)  (hp0 : 0 < f p)  (hp1 : f p < 1)
  (hmin : ∀ (m : ℕ), 0 < f m ∧ f m < 1 → p ≤ m)

private lemma one_lt_of_ne_zero_one {a : ℕ} (ne_0 : a ≠ 0) (ne_1 : a ≠ 1) : 1 < a := by
  rcases a with _ | a
  · exact (ne_0 rfl).elim
  · rw [Nat.succ_ne_succ, ← pos_iff_ne_zero] at ne_1
    exact Nat.succ_lt_succ ne_1

include hp1 hp0 hmin in
 /-- The minimal positive integer with absolute value smaller than 1 is a prime number-/
lemma p_is_prime : (Prime p) := by
  rw [← Nat.irreducible_iff_prime]
  constructor
  · rw [Nat.isUnit_iff]
    intro p1
    simp only [p1, Nat.cast_one, map_one, lt_self_iff_false] at hp1
  · intro a b hab
    rw [Nat.isUnit_iff, Nat.isUnit_iff]
    by_contra con
    push_neg at con
    obtain ⟨a_neq_1, b_neq_1⟩ := con
    apply not_le_of_lt hp1
    rw [hab]
    simp only [Nat.cast_mul, map_mul]
    have neq_0 {a b : ℕ} (hab : p = a * b) : a ≠ 0 := by
      intro an0
      rw [an0, zero_mul] at hab
      rw [hab] at hp0
      rw_mod_cast [map_zero] at hp0
      simp only [lt_self_iff_false] at hp0
    have one_le_f (a b : ℕ) (hab : p = a * b) (one_lt_b : 1 < b) : 1 ≤ f a := by
      by_contra ca
      apply lt_of_not_ge at ca
      apply (@not_le_of_gt _ _ p a)
      · rw [hab, gt_iff_lt]
        exact lt_mul_of_one_lt_right ((pos_iff_ne_zero ).2 (neq_0 hab)) one_lt_b
      · apply hmin
        refine ⟨?_ ,ca⟩
        apply map_pos_of_ne_zero
        exact_mod_cast (neq_0 hab)
    have hba : p = b * a := by
      rw [mul_comm]
      exact hab
    apply one_le_mul_of_one_le_of_one_le
    · exact one_le_f a b hab (one_lt_of_ne_zero_one (neq_0 hba) b_neq_1)
    · exact one_le_f b a hba (one_lt_of_ne_zero_one (neq_0 hab) a_neq_1)

-- ## Step 3
include bdd hp0 hp1 hmin in
/-- a natural number not divible by p has absolute value 1 -/
lemma not_divisible_norm_one (m : ℕ) (hpm : ¬ p ∣ m ) : f m = 1 := by
  rw [le_antisymm_iff]
  refine ⟨bdd m, ?_ ⟩
  by_contra hm
  apply lt_of_not_le at hm
  set M := (f p) ⊔ (f m) with hM
  set k := Nat.ceil (Real.logb  M (1 / 2) ) + 1 with hk
  have hcopr : IsCoprime (p ^ k : ℤ) (m ^ k) := by
    apply IsCoprime.pow (Nat.Coprime.isCoprime _)
    rw [Nat.Prime.coprime_iff_not_dvd (Prime.nat_prime (p_is_prime p hp0 hp1 hmin))]
    exact_mod_cast hpm
  obtain ⟨a, b, bezout⟩ := hcopr
  have le_half x (hx0 : 0 < x) (hx1 : x < 1) (hxM : x ≤ M) : x ^ k < 1/2 := by
    calc
    x ^ k = x ^ (k : ℝ) := by norm_cast
    _ < x ^ Real.logb M (1 / 2) := by
      apply Real.rpow_lt_rpow_of_exponent_gt hx0 hx1
      rw [hk]
      apply lt_of_le_of_lt (Nat.le_ceil (Real.logb M (1/2)))
      norm_cast
      exact lt_add_one ⌈Real.logb M (1 / 2)⌉₊
    _ ≤ x ^ Real.logb x (1/2) := by
      apply Real.rpow_le_rpow_of_exponent_ge hx0 (le_of_lt hx1)
      simp only [← Real.log_div_log]
      ring_nf
      simp only [one_div, Real.log_inv, neg_mul, neg_le_neg_iff]
      rw [mul_le_mul_left (Real.log_pos one_lt_two)]
      rw [inv_le_inv_of_neg _ ((Real.log_neg_iff hx0).2 hx1)]
      · exact Real.log_le_log hx0 hxM
      · rw [Real.log_neg_iff]
        · rw [hM, sup_lt_iff]
          exact ⟨hp1, hm⟩
        · rw [hM, lt_sup_iff]
          left
          exact hp0
    _ = 1/2 := by
      rw [Real.rpow_logb hx0 (ne_of_lt hx1)]
      simp only [one_div, inv_pos, Nat.ofNat_pos]
  apply lt_irrefl (1 : ℝ)
  calc
    (1:ℝ) = f 1 := by rw [map_one]
    _ = f (a * p ^ k + b * m ^ k) := by
      rw_mod_cast [bezout]
      norm_cast
    _ ≤ f (a * p ^ k) + f (b * m ^ k) := f.add_le' (a * p ^ k) (b * m ^ k)
    _ ≤ 1 * (f p) ^ k + 1 * (f m) ^ k := by
      simp only [map_mul, map_pow, le_refl]
      gcongr
      all_goals rw [← f_of_abs_eq_f]; apply bdd
    _ = (f p) ^ k + (f m) ^ k := by simp only [one_mul]
    _ < 1 := by
      rw [← add_halves (a:=1)]
      apply add_lt_add
      · apply le_half (f ↑p) hp0 hp1
        exact le_sup_left
      · apply le_half (f m) _ hm le_sup_right
        apply map_pos_of_ne_zero
        intro m0
        apply hpm
        rw_mod_cast [m0]
        exact dvd_zero p

-- ## Non-archimedean case: step 4

include hp0 hp1 hmin in
lemma abs_p_eq_p_minus_t : ∃ (t : ℝ), 0 < t ∧ f p = p^(-t) := by
  use - Real.logb p (f p)
  have pprime : Nat.Prime p := (Prime.nat_prime (p_is_prime p hp0 hp1 hmin))
  constructor
  · rw [Left.neg_pos_iff]
    apply Real.logb_neg _ hp0 hp1
    rw [Nat.one_lt_cast]
    exact Nat.Prime.one_lt pprime
  · rw [neg_neg]
    apply (Real.rpow_logb (by exact_mod_cast Nat.Prime.pos pprime) _ hp0).symm
    simp only [ne_eq, Nat.cast_eq_one,Nat.Prime.ne_one pprime, not_false_eq_true]



end steps_2_3_4

-- ## Non-archimedean case: end goal
/--
  If `f` is bounded and not trivial, then it is equivalent to a p-adic absolute value.
-/
theorem bdd_implies_equiv_padic (bdd: ∀ n : ℕ, f n ≤ 1) (hf_nontriv : f ≠ 1) :
∃ p, ∃ (hp : Fact (Nat.Prime p)), MulRingNorm.equiv f (mulRingNorm_padic p) := by
  obtain ⟨p, hfp, hmin⟩ := p_exists bdd hf_nontriv
  have hprime : Prime p := p_is_prime p hfp.1 hfp.2 hmin
  use p
  have hprime_fact : Fact (Nat.Prime p) := fact_iff.2 (Prime.nat_prime hprime)
  use (hprime_fact)
  obtain ⟨t, h⟩ := abs_p_eq_p_minus_t p hfp.1 hfp.2 hmin
  rw [← NormRat_equiv_iff_equiv_on_Nat]
  use (t⁻¹)
  refine ⟨by simp only [one_div, inv_pos, h.1], ?_ ⟩
  have oneovertnezero : t⁻¹ ≠ 0 := by
    simp only [ne_eq, inv_eq_zero]
    linarith [h.1]
  intro n
  by_cases hn : n=0
  · rw [hn]
    simp only [CharP.cast_eq_zero, map_zero, ne_eq, oneovertnezero, not_false_eq_true,
      Real.zero_rpow]
  · push_neg at hn
    rcases Nat.exists_eq_pow_mul_and_not_dvd hn p (Nat.Prime.ne_one (Prime.nat_prime hprime))
      with ⟨ e, m, hpm, hnpm⟩
    rw [hnpm]
    simp only [Nat.cast_mul, Nat.cast_pow, map_mul, map_pow, mul_ring_norm_eq_padic_norm,
      padicNorm.padicNorm_p_of_prime, Rat.cast_inv, Rat.cast_natCast, inv_pow]
    rw [not_divisible_norm_one bdd p hfp.1 hfp.2 hmin m hpm, h.2]
    rw [← padicNorm.nat_eq_one_iff] at hpm
    rw [hpm]
    simp only [mul_one, Rat.cast_one]
    rw [← Real.rpow_natCast_mul (Real.rpow_nonneg (Nat.cast_nonneg p) _ ),
      ← Real.rpow_mul (Nat.cast_nonneg p), mul_comm ↑e t⁻¹, ← mul_assoc]
    simp only [neg_mul]
    rw [mul_inv_cancel₀ (by linarith only [h.1]), one_mul, Real.rpow_neg (Nat.cast_nonneg p),
      Real.rpow_natCast]

end Nonarchimedean

/-- Ostrowski's Theorem -/
theorem ringNorm_padic_or_real (f : MulRingNorm ℚ) (hf_nontriv : f ≠ 1) :
    (MulRingNorm.equiv f mulRingNorm_real) ∨
    ∃ (p : ℕ) (hp : Fact (Nat.Prime p)), MulRingNorm.equiv f (@mulRingNorm_padic p hp) := by
  by_cases bdd : ∀ n : ℕ, f n ≤ 1
  · right
    apply bdd_implies_equiv_padic bdd hf_nontriv
  · left
    apply mulRingNorm_equiv_standard_of_unbounded bdd


lemma fooN {n : ℕ} (h_nezero : n ≠ 0) : (Function.mulSupport fun p : Nat.Primes => padicNorm p ↑n).Finite := by
  convert_to { (p : Nat.Primes) | ((p : ℕ) ∣ n) }.Finite
  · ext p
    have : Fact (Nat.Prime ↑p) := by
      refine { out := ?out }
      exact p.2
    have := padicNorm.of_nat (p:= ↑p) n
    simp only [Function.mem_mulSupport, ne_eq, Set.mem_setOf_eq]
    rw [← padicNorm.nat_lt_one_iff]
    refine ⟨lt_of_le_of_ne this, ne_of_lt ⟩
  · let f : Nat.Primes → ℕ := fun a => ↑a
    let s := {p : Nat.Primes | ↑p ∣ n}
    have : (f '' s).Finite := by
      apply Set.Finite.subset (Set.finite_le_nat n)
      simp only [Set.image_subset_iff, Set.preimage_setOf_eq]
      exact Set.setOf_subset_setOf.mpr (fun p hp => Nat.le_of_dvd (Nat.zero_lt_of_ne_zero h_nezero) hp)
    apply Set.Finite.of_finite_image this
    refine Function.Injective.injOn ?h
    exact Nat.Primes.coe_nat_injective

lemma fooZ {n : ℤ} (h_nezero : n ≠ 0) : (Function.mulSupport fun p : Nat.Primes => padicNorm ↑p ↑n).Finite := by
  have habs := Int.natAbs_eq n
  cases habs with
  | inl h =>
    rw [h]
    apply_mod_cast fooN (Int.natAbs_ne_zero.mpr h_nezero)
  | inr h =>
    rw [h]
    simp only [Int.cast_neg, Int.cast_abs, padicNorm.neg]
    apply_mod_cast fooN (Int.natAbs_ne_zero.mpr h_nezero)

theorem product_formula_N {x : ℕ} (h_x_nezero : x ≠ 0) : |(x : ℚ)| * ∏ᶠ p : Nat.Primes, padicNorm p x = 1 := by
  rw [← Nat.factorization_prod_pow_eq_self h_x_nezero]
  sorry

theorem product_formula_Z {x : ℤ} (h_x_nezero : x ≠ 0) : |(x : ℚ)| * ∏ᶠ p : Nat.Primes, padicNorm p x = 1 := by
  have habs := Int.natAbs_eq x
  cases habs with
  | inl h =>
    rw [h]
    apply product_formula_N (Int.natAbs_ne_zero.mpr h_x_nezero)
  | inr h =>
    rw [h]
    simp only [Int.cast_neg, Int.cast_abs, abs_neg, abs_abs, padicNorm.neg]
    apply product_formula_N (Int.natAbs_ne_zero.mpr h_x_nezero)

theorem product_formula {x : ℚ} (h_x_nezero : x ≠ 0) : |x| * ∏ᶠ p : Nat.Primes, padicNorm p x = 1 := by
  --UniqueFactorizationMonoid.factors_pow_count_prod
  --
  -- does not work: rw [padicNorm.div ↑x.num ↑x.den]
  --finprod_congr
  rw [← Rat.num_div_den x, abs_div]
  --simp_rw [padicNorm.eq_zpow_of_nonzero]
  have (p : Nat.Primes) : padicNorm p (↑x.num / ↑x.den) = padicNorm p (↑x.num) / padicNorm p (↑x.den) := by
    have : Fact (Nat.Prime ↑p) := by
      refine { out := ?out }
      exact p.2
    exact padicNorm.div ↑x.num ↑x.den
  rw [finprod_congr this, finprod_div_distrib (fooZ (Rat.num_ne_zero.mpr h_x_nezero))
    (mod_cast fooZ (mod_cast x.den_nz)),← mul_div_assoc, mul_comm, mul_div_assoc,
    ← div_mul_eq_div_div, ← mul_div_assoc]
  nth_rw 1 [mul_comm]
  rw [product_formula_Z (Rat.num_ne_zero.mpr h_x_nezero), product_formula_N x.den_nz]
  exact one_div_one

end Rational
