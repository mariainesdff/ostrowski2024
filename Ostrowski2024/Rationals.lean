
--import Ostrowski2024.Basic
import Ostrowski2024.MulRingNormRat
--import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
--import Mathlib.Analysis.SpecialFunctions.Pow.Real
-- import Mathlib.Algebra.Order.Monoid.Lemmas

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

/- Multiplication by a constant moves in a List.sum -/
lemma list_mul_sum {R : Type*} [CommSemiring R] {T : Type*} (l : List T) (y : R) : ∀ x : R ,
    List.sum (List.mapIdx (fun i _ => x * y ^ i) (l)) =
    x * List.sum (List.mapIdx (fun i _ => y ^ i) (l)) := by
  induction l with
  | nil => simp only [List.mapIdx_nil, List.sum_nil, mul_zero, forall_const]
  | cons head tail ih =>
    intro x
    simp_rw [List.mapIdx_cons, pow_zero, mul_one, List.sum_cons, mul_add, mul_one]
    have (a : ℕ ) : y ^ (a + 1) = y * y ^ a := by ring
    simp_rw [this, ← mul_assoc, ih, ← mul_assoc]

/- Geometric sum for lists -/
lemma list_geom {T : Type*} {F : Type*} [Field F] (l : List T) (y : F ) (hy : y ≠ 1) :
    List.sum (List.mapIdx (fun i _ => y ^ i) l) = (y ^ l.length - 1) / (y - 1) := by
  induction l with
  | nil => simp only [List.mapIdx_nil, List.sum_nil, List.length_nil, pow_zero, sub_self, zero_div]
  | cons head tail ih =>
    simp only [List.mapIdx_cons, pow_zero, List.sum_cons, List.length_cons]
    have (a : ℕ ) : y ^ (a + 1) = y * y ^ a := by ring
    simp_rw [this,list_mul_sum, ih]
    simp only [mul_div,← same_add_div (sub_ne_zero.2 hy), mul_sub, mul_one, sub_add_sub_cancel']

/- Triangle inequality for absolute values applied to a List. -/
lemma mulRingNorm_sum_le_sum_mulRingNorm {R : Type*} [Ring R] (l : List R) (f : MulRingNorm R) :
    f l.sum ≤ (l.map f).sum := by
  induction l with
  | nil => simp only [List.sum_nil, map_zero, List.map_nil, le_refl]
  | cons head tail ih =>
    simp only [List.sum_cons, List.map_cons]
    calc f (head + List.sum tail) ≤ f head + f (List.sum tail) := by apply f.add_le'
      _ ≤ f head + List.sum (List.map (⇑f) tail) := by simp only [add_le_add_iff_left, ih]

lemma MulRingNorm_digit_lt_base {R : Type*} [Ring R] (f : MulRingNorm R) (m c n : ℕ)
    (h_one_lt_m : 1 < m) (hcdig: c ∈ Nat.digits m (n)) : f c < m := by
  apply lt_of_le_of_lt (MulRingNorm_nat_le_nat c f)
  exact_mod_cast Nat.digits_lt_base h_one_lt_m hcdig

/-- Given an two integers `n m` the absolute value of `n` is bounded by
    `m + m * f m + m * (f m) ^ 2 + ... + m * (f m) ^ d`.-/
lemma MulRingNorm_n_le_sum_digits (n : ℕ) {m : ℕ} (hm : 1 < m):
    f n ≤ ((Nat.digits m n).mapIdx fun i _ => m * (f m) ^ i).sum := by
  set L := Nat.digits m n with hL
  set L' : List ℚ := List.map Nat.cast (L.mapIdx fun i a => (a * m ^ i)) with hL'
  have hcoef (c : ℕ) (hc : c ∈ Nat.digits m n) : f c < m := MulRingNorm_digit_lt_base f m c n hm hc
  calc
  f n = f ((Nat.ofDigits m L : ℕ) : ℚ) := by rw [hL, Nat.ofDigits_digits m n]
    _ = f (L'.sum) := by
          rw [Nat.ofDigits_eq_sum_mapIdx, hL']
          norm_cast
    _ ≤ (L'.map f).sum := mulRingNorm_sum_le_sum_mulRingNorm L' f
    _ ≤ (L.mapIdx fun i _ => m * (f m) ^ i).sum := by
      simp only [hL', List.mapIdx_eq_enum_map, List.map_map]
      apply List.sum_le_sum
      rintro ⟨i,a⟩ hia
      dsimp [Function.uncurry]
      replace hia := List.mem_enumFrom L hia
      push_cast
      rw [map_mul, map_pow]
      apply mul_le_mul_of_nonneg_right (le_of_lt (hcoef a hia.2.2)) (by simp only [ge_iff_le,
        apply_nonneg, pow_nonneg])

open BigOperators

/- ## Auxiliary lemma for limits-/
/-- If `a : ℝ` is bounded above by a function `g : ℕ → ℝ` for every `0 < k` then it is less or
equal than the limit `lim_{k → ∞} g(k)`-/
lemma le_of_limit_le (a : ℝ) (g : ℕ → ℝ) (l : ℝ) (ha : ∀ (k : ℕ) (_ : 0 < k), a ≤ g k)
  (hg : Filter.Tendsto g Filter.atTop (nhds l) ) : a ≤ l := by
  apply le_of_tendsto_of_tendsto tendsto_const_nhds hg
  rw [Filter.EventuallyLE, Filter.eventually_atTop]
  exact ⟨1, ha⟩


/-- For any `C > 0`, the limit of `C ^ (1/k)` is 1 as `k → ∞`. -/
lemma tendsto_root_atTop_nhds_one (C : ℝ) (hC : 0 < C) : Filter.Tendsto
    (fun k : ℕ ↦ (C ^ (1 / (k : ℝ)))) Filter.atTop (nhds 1) := by
  rw [← Real.exp_log hC]
  simp_rw [← Real.exp_mul]
  refine Real.tendsto_exp_nhds_zero_nhds_one.comp ?_
  simp_rw [mul_one_div]
  apply tendsto_const_div_atTop_nhds_zero_nat

/-- The function `(n₀ * ((Real.logb n₀ n) + 1))^(k⁻¹)` tends to `1` as `k → ∞`. -/
lemma tendsto_root_mul_log_add_one_atTop_nhds_one (n₀ n : ℕ) (hn₀ : 1 < n₀) (hn : 1 < n) :
    Filter.Tendsto (fun k : ℕ ↦ (n₀ * (Real.logb n₀ n + 1)) ^ (k : ℝ)⁻¹)
    Filter.atTop (nhds 1) := by
  simp_rw [← one_div]
  apply tendsto_root_atTop_nhds_one (n₀ * (Real.logb n₀ n + 1))
  apply mul_pos (mod_cast (lt_trans zero_lt_one hn₀))
  exact add_pos (Real.logb_pos (mod_cast hn₀) (mod_cast hn)) Real.zero_lt_one

/-extends the lemma `tendsto_rpow_div` when the function has natural input-/
lemma tendsto_nat_rpow_div : Filter.Tendsto (fun k : ℕ ↦ (k : ℝ) ^ (k : ℝ)⁻¹)
    Filter.atTop (nhds 1) := by
  simp only [Filter.tendsto_def, Filter.mem_atTop_sets, ge_iff_le, Set.mem_preimage]
  intro N hN
  let h := tendsto_rpow_div
  simp only [Filter.tendsto_def, one_div, Filter.mem_atTop_sets, ge_iff_le, Set.mem_preimage] at h
  rcases (h N hN) with ⟨a, ha⟩
  use (Nat.floor a) + 1
  intro b hb
  exact (ha b) (le_trans (le_of_lt (Nat.lt_floor_add_one a)) (mod_cast hb))

-- ## step 1
--

/-- `Nat.log` is less or equal then `Real.log`. -/
lemma nat_log_le_real_log (a b : ℕ) (_ : 0 < a) (hb : 1 < b) : Nat.log b a ≤ Real.logb b a := by
  apply le_trans _ (Int.floor_le ((b : ℝ).logb (a : ℝ)))
  simp only [Real.floor_logb_natCast hb (Nat.cast_nonneg a), Int.log_natCast, Int.cast_natCast,
     le_refl]

open Nat

lemma List.sum_le_of_entry_le (l : List ℝ) (m : ℝ)
    (h : ∀ a ∈ l, a ≤ m) : l.sum ≤ m * l.length := by
  induction l with
  | nil => simp only [List.sum_nil, List.length_nil, cast_zero, mul_zero, le_refl]
  | cons head tail ih =>
    simp only [List.sum_cons, List.length_cons, succ_eq_add_one, cast_add, cast_one, mul_add,
      mul_one, add_comm]
    simp only [List.mem_cons, forall_eq_or_imp] at h
    gcongr
    exact h.1
    exact ih h.2

/-- If `f n > 1` for some `n` then `f n > 1` for all `n ≥ 2`.-/
lemma one_lt_of_notbdd (notbdd : ¬ ∀ (n : ℕ), f n ≤ 1) (n₀ : ℕ) : 1 < n₀ → 1 < f n₀ := by
  contrapose! notbdd with h
  rcases h with ⟨hn₀, hfn₀⟩
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
      exact mul_le_of_le_of_le_one' (mod_cast le_refl n₀) (pow_le_one i (apply_nonneg f ↑n₀) hfn₀)
        (pow_nonneg (apply_nonneg f ↑n₀) i) (cast_nonneg n₀)
    _ ≤ n₀ * (Real.logb n₀ m + 1) := by
      rw [List.mapIdx_eq_enum_map, List.eq_replicate_of_mem (a := (n₀ : ℝ))
        (l := List.map (Function.uncurry fun _ _ => n₀) (List.enum L)),
        List.sum_replicate, List.length_map, List.enum_length, nsmul_eq_mul, mul_comm]
      · rw [Nat.digits_len n₀ m hn₀ (not_eq_zero_of_lt hm)]
        apply mul_le_mul_of_nonneg_left _ (cast_nonneg n₀)
        push_cast
        simp only [add_le_add_iff_right]
        exact nat_log_le_real_log m n₀ hm hn₀
      · simp_all only [List.mem_map, Prod.exists, Function.uncurry_apply_pair, exists_and_right,
          and_imp, implies_true, forall_exists_index, forall_const]
  -- For h_ineq2 we need to exclude the case n = 0.
  rcases eq_or_ne n 0 with rfl | h₀; simp only [CharP.cast_eq_zero, map_zero, zero_le_one]
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
        Filter.atTop (nhds 1) := tendsto_root_mul_log_add_one_atTop_nhds_one n₀ n hn₀
        (lt_of_le_of_ne (one_le_iff_ne_zero.mpr h₀) (id (Ne.symm h₁)))
    exact Filter.Tendsto.mul hnlim tendsto_nat_rpow_div
  exact le_of_limit_le (f n) (fun k : ℕ ↦ (n₀ * (Real.logb n₀ n + 1)) ^ (k : ℝ)⁻¹ * (k^(k : ℝ)⁻¹))
    1 h_ineq2 prod_limit

-- ## step 2
-- given m,n \geq 2 and |m|=m^s, |n|=n^t for s,t >0, prove t \leq s
section Step2

open Real
open BigOperators

variable (m n : ℕ) (hm : 1 < m) (hn : 1 < n) (notbdd: ¬ ∀(n : ℕ), f n ≤ 1)

private lemma main_inequality : f n ≤ (m * f m / (f m - 1)) * (f m ^ logb m n) := by
  have hfm : 1 < f m := one_lt_of_notbdd notbdd m hm
  let d := Nat.log m n
  calc f n ≤ ((Nat.digits m n).mapIdx fun i _ ↦ m * (f m) ^ i).sum :=
    MulRingNorm_n_le_sum_digits n hm
    _ = m * ((Nat.digits m (n)).mapIdx fun i _ ↦ (f m) ^ i).sum :=
      list_mul_sum (m.digits n) (f m) m
    _ = m * ((f m ^ (d + 1) - 1) / (f m - 1)) := by
      rw [list_geom _ (f m) (ne_of_gt (hfm)), (Nat.digits_len m n hm (not_eq_zero_of_lt hn)).symm]
    _ ≤ m * ((f m ^ (d + 1))/(f m - 1)) := by gcongr; linarith only [hfm]; linarith only
    _ = ↑m * f ↑m / (f ↑m - 1) * f ↑m ^ d := by ring
    _ ≤ ↑m * f ↑m / (f ↑m - 1) * f ↑m ^ logb ↑m ↑n := by
      gcongr
      exact div_nonneg (mul_nonneg (by linarith only [hm]) (by linarith only [hfm]))
        (by linarith only [hfm])
      rw [← Real.rpow_natCast]
      apply Real.rpow_le_rpow_of_exponent_le (le_of_lt hfm)
      apply nat_log_le_real_log n m (zero_lt_of_lt hn) hm



lemma logb_pow (k m n : ℕ) : logb m (n ^ k) = k * logb m n := by
  simp only [logb, Real.log_pow, mul_div]


/-
lemma move_pow (A B : ℝ) (hA : 0 ≤ A) (k : ℝ) (hk : 0 < k) (hle : A ^ k ≤ B) : A ≤ B ^ (1/(k:ℝ)) := by
  have : (A ^ (k : ℝ)) ^ (1 / (k : ℝ)) = A := by
    rw [← rpow_mul, mul_one_div, div_self, rpow_one]; exact ne_of_gt hk; assumption
  rw[← this]
  refine rpow_le_rpow (rpow_nonneg hA k) hle ?_
  apply le_of_lt
  simp only [one_div, inv_pos]
  exact hk -/


lemma param_upperbound (k : ℕ) (hk : k ≠ 0) :
    f n ≤ (m * (f m) / ((f m) - 1)) ^ (1 / (k : ℝ)) * ((f m) ^ (logb m n)) := by
  -- the "power trick"
  have key : (f n) ^ k ≤ (m * (f m) / ((f m) - 1)) * ((f m) ^ (k * logb m n)) :=
  calc
    (f n) ^ k
    = f (↑(n ^ k)) := by simp only [map_pow, Nat.cast_pow]
    _ ≤ (m * (f m) / ((f m) - 1)) * ((f m) ^ (logb (↑ m) (↑(n ^ k)))) :=
        main_inequality m (n ^ k) hm (one_lt_pow hn hk) notbdd
    _ = (m * (f m) / ((f m) - 1)) * ((f m) ^ (k * logb (↑ m) (↑(n)))) :=
      by { push_cast; rw [logb_pow]}
  obtain h := one_lt_of_notbdd notbdd
  have : 1 < f m := by simp only [h m hm]
  have  zero_le_expression: 0 ≤ ↑m * f ↑m / (f ↑m - 1) := by
    apply div_nonneg _ (by linarith only [this])
    apply mul_nonneg (Nat.cast_nonneg m) (apply_nonneg f ↑m)
  have triviality : (1 / k) * (k : ℝ) = 1 := by
      apply one_div_mul_cancel
      exact_mod_cast hk
  have our_prod_nonneg :  0 ≤ ↑m * f ↑m / (f ↑m - 1) * f ↑m ^ (↑k * logb ↑m ↑n) := by
      rw [mul_nonneg_iff_of_pos_right]
      exact zero_le_expression
      apply Real.rpow_pos_of_pos
      linarith only [this]
  convert_to f ↑n ≤ ((↑m * f ↑m / (f ↑m - 1)) * f ↑m ^ (k * logb ↑m ↑n))^ (1 / k : ℝ )
  · rw [Real.mul_rpow]
    simp only [mul_eq_mul_left_iff]
    left
    rw [← rpow_mul (apply_nonneg f ↑m), mul_comm, ← mul_assoc]
    rw [triviality]
    simp only [one_mul]
    exact zero_le_expression
    apply rpow_nonneg (apply_nonneg f ↑m)
  · rw [← Real.rpow_le_rpow_iff (z:=k ) _  ]
    · rw [← rpow_mul, triviality, rpow_natCast, rpow_one]
      exact key
      exact our_prod_nonneg
    · apply rpow_nonneg
      exact our_prod_nonneg
    · simp only [Nat.cast_pos.2 (Nat.pos_of_ne_zero hk)]
    · exact (apply_nonneg f ↑n)




/- If A ≤ (C k) * B for all k, then A ≤ limC * B, where limC is the limit of the sequence C.
-- TODO: can be generalized but we only need it here for sequences of reals.


lemma le_mul_of_le_fun_mul' {A B : ℝ} {C : ℕ → ℝ} {limC : ℝ} {x : Filter ℕ} [Filter.NeBot x]
  (lim : Filter.Tendsto C x (nhds limC)) (h : ∀ k, A ≤ (C k) * B) : A ≤ limC * B := by
    have limCB : Filter.Tendsto (fun k ↦ (C k) * B) x (nhds (limC * B)) := by
      refine Filter.Tendsto.mul_const B lim
    refine (ge_of_tendsto' limCB h)


 lemma le_of_le_mul_root {A B C : ℝ} (hC : 0 < C) (hub : ∀ (k : ℕ), A ≤ C ^ (1 / (k:ℝ)) * B) :
     A ≤ B := by
  rw [← one_mul B]
  apply le_mul_of_le_fun_mul' (tendsto_root_atTop_nhds_one C hC)
  exact hub
 -/

open Filter

lemma le_mul_of_le_fun_mul {A B : ℝ} {C : ℕ → ℝ} {limC : ℝ} (lim : Tendsto C atTop (nhds limC))
    (h : ∀ k, k ≠ 0 → A ≤ C k * B) : A ≤ limC * B := by
  apply ge_of_tendsto (Tendsto.mul_const B lim)
  rw [eventually_iff_exists_mem]
  use {b | 1 ≤ b}
  constructor
  · simp only [mem_atTop_sets, ge_iff_le, Set.mem_setOf_eq]
    exact ⟨1, fun b a ↦ a⟩
  · simp only [Set.mem_setOf_eq]
    intro y hy
    exact h y (not_eq_zero_of_lt hy)

lemma le_of_le_mul_root {A B C : ℝ} (hC : 0 < C)
    (hub : ∀ (k : ℕ),k ≠ 0 →  A ≤ C ^ (1 / (k : ℝ)) * B) : A ≤ B := by
  rw [← one_mul B]
  exact le_mul_of_le_fun_mul (tendsto_root_atTop_nhds_one C hC) hub


lemma mulRingNorm_le_mulRingNorm_pow_log : f n ≤ (f m) ^ (logb m n) := by
  have zero_lt_A : 0 < m * (f m) / ((f m) - 1) := by
    apply div_pos (mul_pos (mod_cast zero_lt_of_lt hm)
      (map_pos_of_ne_zero f (mod_cast ne_zero_of_lt hm)))
    linarith only [one_lt_of_notbdd notbdd m hm]
  refine le_of_le_mul_root (zero_lt_A) ?_
  intro k hk
  exact param_upperbound m n hm hn notbdd k hk


lemma compare_exponents (s t : ℝ) (hfm : f m = m ^ s) (hfn : f n = n ^ t)  : t ≤ s := by
    have hmn : f n ≤ (f m)^(Real.logb m n) := mulRingNorm_le_mulRingNorm_pow_log m n hm hn notbdd
    rw [← Real.rpow_le_rpow_left_iff (x:=n)]
    · rw[← hfn]
      rw [hfm] at hmn
      rw [← Real.rpow_mul] at hmn
      · rw [mul_comm] at hmn
        rw [Real.rpow_mul] at hmn
        · rw [Real.rpow_logb] at hmn
          · exact hmn
          · simp only [Nat.cast_pos]
            linarith only [hm]
          · simp only [ne_eq, Nat.cast_eq_one]
            linarith only [hm]
          · simp only [Nat.cast_pos]
            linarith only [hn]
        · simp only [Nat.cast_nonneg]
      · simp only [Nat.cast_nonneg]
    · exact_mod_cast hn


lemma symmetric_roles (s t : ℝ)
  (hfm : f m = m ^ s) (hfn : f n = n ^ t) : s = t := by
  apply le_antisymm
  refine compare_exponents _ _ hn hm notbdd t s hfn hfm
  refine compare_exponents _ _ hm hn notbdd s t  hfm hfn

end Step2

-- ## final step
-- finish the proof by symmetry (exchanging m,n and proving s \leq t) TODO


-- ## Archimedean case: end goal
/--
   If `f` is not bounded and not trivial, then it is equivalent to the usual absolute value on ℚ.
-/



theorem notbdd_implies_equiv_real (notbdd: ¬ ∀ (n : ℕ), f n ≤ 1)  : MulRingNorm.equiv f mulRingNorm_real := by
  obtain ⟨m, hm⟩ := Classical.exists_not_of_not_forall notbdd
  have oneltm : 1 < m := by
    by_contra!
    apply hm
    replace this : m = 0 ∨ m = 1 := by omega
    rcases this with (rfl | rfl )
    all_goals simp only [CharP.cast_eq_zero, map_zero, zero_le_one,Nat.cast_one, map_one, le_refl]
  rw [← NormRat_equiv_iff_equiv_on_Nat]
  set s := Real.logb m (f m) with hs
  use s⁻¹
  constructor
  · rw [hs,inv_pos]
    apply Real.logb_pos (Nat.one_lt_cast.2 oneltm) (by linarith only [hm])
  · intro n
    by_cases nzero : n = 0
    · rw [nzero]
      simp only [CharP.cast_eq_zero, map_zero, le_refl]
      rw [Real.rpow_eq_zero (le_rfl)]
      rw [hs]
      simp only [ne_eq, inv_eq_zero, Real.logb_eq_zero, Nat.cast_eq_zero, Nat.cast_eq_one,
        map_eq_zero]
      push_neg
      norm_cast
      simp only [not_false_eq_true, Int.reduceNegSucc, Int.cast_neg, Int.cast_one, true_and]
      refine ⟨by  omega, by  omega, by  omega, by linarith only [hm], by linarith only [hm]⟩
    · by_cases none : n=1
      · rw [none]
        simp only [Nat.cast_one, map_one, Real.one_rpow]
      · have oneltn : 1 < n := by omega
        have fngeone : 1 < f n := one_lt_of_notbdd notbdd _ oneltn
        set t := Real.logb n (f n) with ht
        have hm' : (f m )= m ^ s := by
          rw [hs,Real.rpow_logb _ _ (by linarith only [hm]) ]
          all_goals norm_cast
          all_goals omega
        have hn : (f n )= n ^ t := by
          rw [ht,Real.rpow_logb _ _ (by linarith only [fngeone]) ]
          all_goals norm_cast
          all_goals omega
        have seqt : s = t := by
          exact symmetric_roles _ _ oneltm oneltn notbdd _ _ hm' hn
        rw [seqt,hn]
        simp only [Nat.cast_nonneg, mul_ring_norm_eq_abs, Nat.abs_cast, Rat.cast_natCast]
        rw [← Real.rpow_mul (by linarith only [nzero])]
        convert Real.rpow_one _
        apply mul_inv_cancel
        rw [ht]
        exact Real.logb_ne_zero_of_pos_of_ne_one (by assumption_mod_cast) (by positivity) (by linarith only [fngeone])


end Archimedean

section Nonarchimedean

section step_1

-- ## Non-archimedean: step 1 define `p = smallest n s. t. 0 < |n| < 1`

variable (bdd: ∀ n : ℕ, f n ≤ 1)

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
/-- a natural number not divible by p has absolute value 1 -/
lemma not_divisible_norm_one (m : ℕ) (hpm : ¬ p ∣ m ) : f m = 1 := by
  rw [le_antisymm_iff]
  refine ⟨bdd m, ?_ ⟩
  by_contra hm
  apply lt_of_not_le at hm
  set M := (f p) ⊔ (f m) with hM
  set k := Nat.ceil ( Real.logb  M (1/2) ) + 1 with hk
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
    rw [mul_inv_cancel (by linarith only [h.1]), one_mul, Real.rpow_neg (Nat.cast_nonneg p),
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
    apply notbdd_implies_equiv_real bdd

end Rational
