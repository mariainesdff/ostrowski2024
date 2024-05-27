
--import Ostrowski2024.Basic
import Ostrowski2024.MulRingNormRat
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Real
-- import Mathlib.Algebra.Order.Monoid.Lemmas

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

--Not used
/- lemma mul_ring_norm.padic_is_nonarchimedean (p : ℕ) [hp : Fact (Nat.Prime p)] (a b : ℚ) :
    mulRingNorm_padic p (a + b) ≤ max (mulRingNorm_padic p a) (mulRingNorm_padic p b) := by
  rw [mul_ring_norm_eq_padic_norm]
  rw [mul_ring_norm_eq_padic_norm]
  rw [mul_ring_norm_eq_padic_norm]
  norm_cast
  exact padicNorm.nonarchimedean
  done -/

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
    simp only [List.mapIdx_cons, pow_zero, mul_one, List.sum_cons]
    rw [mul_add]
    simp only [mul_one, add_right_inj]
    have (a : ℕ ) : y ^ (a + 1) = y * y ^ a := by ring
    simp_rw [this, ← mul_assoc, ih,← mul_assoc]

/- Geometric sum for lists -/
lemma list_geom {T : Type*} {F : Type*} [Field F] (l : List T) (y : F ) (hy : y ≠ 1) :
    List.sum (List.mapIdx (fun i _ => y ^ i) l) = (y ^ l.length - 1) / (y - 1) := by
  induction l with
  | nil => simp only [List.mapIdx_nil, List.sum_nil, List.length_nil, pow_zero, sub_self, zero_div]
  | cons head tail ih =>
    simp only [List.mapIdx_cons, pow_zero, List.sum_cons, List.length_cons]
    have (a : ℕ ) : y ^ (a + 1) = y * y ^ a := by ring
    simp_rw [this,list_mul_sum, ih]
    rw [mul_div,← same_add_div (sub_ne_zero.2 hy), mul_sub]
    simp only [mul_one, sub_add_sub_cancel']

/-Triangle inequality for absolute values applied to Lists-/
lemma MulRingNorm_sum_le_sum_MulRingNorm {R : Type*} [Ring R] (l : List R) (f : MulRingNorm R) :
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


/- #find_home! list_mul_sum
#find_home! list_geom
#find_home! MulRingNorm_sum_le_sum_MulRingNorm -/

/-Given an two integers `n n0` the absolute value of `n` raised to the `k`-th power is bounded by
    `n0 + n0 |n0| + n0 |n0|^2 + ...`-/
lemma mulringnorm_n_pow_k_le_sum_digits_n0 (f: MulRingNorm ℚ) (n0 : ℕ) (hn0_ge2: 1 < n0)
    (n : ℕ) (hn: 1 < n)  (k : ℕ) (hk: 0 < k) (hcoeff: ∀ c ∈ Nat.digits n0 (n ^ k), f ↑c < ↑n0):
    (f n)^k ≤ ((Nat.digits n0 (n^k)).mapIdx fun i _ => n0 * (f n0) ^ i).sum := by
  set L := Nat.digits n0 (n ^ k) with hL
  set L' : List ℚ := List.map Nat.cast (L.mapIdx fun i a => (a * n0 ^ i)) with hL'
  calc
  (f n)^k = f ((Nat.ofDigits n0 L : ℕ) : ℚ) := by
          rw[← map_pow, hL, Nat.ofDigits_digits n0 (n^k), ← Nat.cast_pow]
        _ = f (L'.sum) := by
          rw [Nat.ofDigits_eq_sum_mapIdx, hL']
          norm_cast
        _ ≤ (L'.map f).sum := MulRingNorm_sum_le_sum_MulRingNorm _ _
        _ ≤ (L.mapIdx fun i _ => n0 * (f n0) ^ i).sum := by
              simp only [hL', List.mapIdx_eq_enum_map, List.map_map]
              apply List.sum_le_sum
              rintro ⟨i,a⟩ hia
              dsimp [Function.uncurry]
              replace hia := List.mem_enumFrom _ hia
              push_cast
              rw[map_mul, map_pow]
              exact mul_le_mul (le_of_lt (hcoeff _ hia.2.2)) (by simp only [le_refl]) (by simp only [ge_iff_le,
                apply_nonneg, pow_nonneg]) (by simp only [Nat.cast_nonneg])

open BigOperators



/- ## Auxiliary lemma for limits
    If `a :ℝ` is bounded above by a function `g : ℕ → ℝ` for every `k : ℕ` then it is less or equal than
    the limit `lim_{k → ∞} g(k)`-/

/- lemma forall_le_limit (a : ℝ) (g: ℕ → ℝ) (l:ℝ) (ha: ∀ (k : ℕ),  a ≤ g k)
    (hg: Filter.Tendsto g Filter.atTop (nhds l) ): a ≤ l := by
  set f:= fun _ : ℕ ↦ (a : ℝ)
  have hflim : Filter.Tendsto f Filter.atTop (nhds a) := by exact tendsto_const_nhds
  exact le_of_tendsto_of_tendsto' hflim hg ha -/

/- For the applications we need the same statement with the extra hypothesis that ` a ≤ g(k)` holds
    for every `k > 0`. This is done using the notion of `eventually less`
-/
lemma forall_le_limit (a : ℝ) (g : ℕ → ℝ) (l : ℝ) (ha : ∀ (k : ℕ) (_ : 0 < k), a ≤ g k)
  (hg : Filter.Tendsto g Filter.atTop (nhds l) ) : a ≤ l := by
  set f := fun _ : ℕ ↦ (a : ℝ) with hf
  have hflim : Filter.Tendsto f Filter.atTop (nhds a) := by exact tendsto_const_nhds
  apply le_of_tendsto_of_tendsto hflim hg _
  rw [Filter.EventuallyLE, Filter.eventually_atTop]
  use 1
  intro m hm
  simp only [hf]
  exact ha m hm

/-- For any C > 1, the limit of C ^ (1/k) is 1 as k -> ∞. -/
lemma one_lim_of_roots (C : ℝ) (hC : 0 < C) : Filter.Tendsto
 (fun k : ℕ ↦ (C ^ (1 / (k : ℝ)))) Filter.atTop (nhds 1) := by
  rw [← Real.exp_log hC]
  simp_rw [← Real.exp_mul]
  refine Real.tendsto_exp_nhds_zero_nhds_one.comp ?_
  simp_rw [mul_one_div]
  apply tendsto_const_div_atTop_nhds_zero_nat

/- the function `(n0 * ((Real.logb n0 n) + 1))^k^⁻¹` tends to `1` as `k → ∞`-/
lemma one_lim_kroot_log_expr (n0 n : ℕ) (hn0_ge2: 1 < n0) (hn : 1 < n) :
    Filter.Tendsto (fun k : ℕ ↦ (n0 * (Real.logb (↑ n0) (↑n) + 1)) ^ ((k:ℝ)⁻¹))
    Filter.atTop (nhds 1) := by
  have hpos : 0 < (n0 * (Real.logb (↑ n0) (↑n) + 1)) := by
    rw[mul_pos_iff]
    left
    constructor
    norm_cast
    exact (lt_trans zero_lt_one hn0_ge2)
    calc
    0 < Real.logb ↑n0 ↑n := by
      rw[Real.logb_pos_iff ?_ ?_]
      simp[hn]
      simp[hn0_ge2]
      simp
      exact (lt_trans zero_lt_one hn)
    _ < Real.logb ↑n0 ↑n + 1 := lt_add_of_pos_right (Real.logb ↑n0 ↑n) zero_lt_one
  convert_to Filter.Tendsto (fun k : ℕ ↦ (n0 * (Real.logb (↑ n0) (↑n) + 1)) ^ (1/(k:ℝ))) Filter.atTop (nhds 1)
  · simp only [one_div]
  apply one_lim_of_roots (n0 * (Real.logb (↑ n0) (↑n) + 1)) hpos



/-extends the lemma `tendsto_rpow_div` when the function has natural input-/
lemma tendsto_nat_rpow_div : Filter.Tendsto (fun k : ℕ ↦ ((k:ℝ) ^ ((k:ℝ)⁻¹)))
    Filter.atTop (nhds 1) := by
  rw [Filter.tendsto_def]
  simp only [Filter.mem_atTop_sets, ge_iff_le, Set.mem_preimage]
  intro N hN
  let h := tendsto_rpow_div
  rw [Filter.tendsto_def] at h
  simp only [one_div, Filter.mem_atTop_sets, ge_iff_le, Set.mem_preimage] at h
  rcases (h N hN) with ⟨a, ha ⟩
  use (Nat.floor a)+1
  intro b hb
  specialize ha b
  apply ha
  calc
  a ≤  ⌊a⌋₊ + 1 := le_of_lt (Nat.lt_floor_add_one a)
  _  ≤ ↑b := by exact_mod_cast hb



-- ## step 1
-- if |n|>1 for some n then |n|>1 for *all* n \geq 2 (by proving contrapositive)

/-`Nat.log` is less or equal then `Real.log`-/
lemma nat_log_le_real_log (n0 n : ℕ) (hn : 0 < n) (hn0 : 1 < n0) : Nat.log n0 n ≤ Real.logb n0 n := by
  have hnat : n0 ^ (Nat.log n0 n) ≤ n := by
    apply Nat.pow_log_le_self
    have : n ≠ 0 := by
      apply ne_of_gt
      assumption
    assumption
  have hreal : (n0:ℝ) ^ (Real.logb n0 n) = n := by
    rw [Real.rpow_logb]
    norm_cast
    linarith only [hn0]
    simp only [ne_eq, Nat.cast_eq_one]
    linarith only [hn0]
    exact_mod_cast hn
  have : n0 ^ (Nat.log n0 n) ≤ (n0 : ℝ)^(Real.logb n0 n ) := by
    rw [hreal]
    exact_mod_cast hnat
  have hn0_gt1R : 1 < (n0:ℝ) := by exact_mod_cast hn0
  rw [← Real.rpow_le_rpow_left_iff hn0_gt1R]
  exact_mod_cast this


open Nat



lemma notbdd_implies_all_gt_one (notbdd : ¬ ∀ (n : ℕ), f n ≤ 1) : ∀ (n : ℕ) (hn : 1 < n),
   f n > 1 := by
  contrapose! notbdd
  rcases notbdd with ⟨n0, hn0_ge2, hfn0⟩
  intro n
  cases' n with n; simp only [Nat.zero_eq, CharP.cast_eq_zero, map_zero, zero_le_one]
  by_cases hn : n = 0; norm_cast; simp only [hn, Nat.reduceSucc, Nat.cast_one, map_one, le_refl]
  have h_one_lt_succ_n : 1 < Nat.succ n := by exact Nat.sub_ne_zero_iff_lt.mp hn

  have hnk {n : ℕ} (hn : 1 < n) {k : ℕ} (hk : 0 < k) :
      (f n)^k ≤ (n0 * (Real.logb n0 (n^k)  + 1)) := by
    /- L is the string of digits of `n` modulo `n0`-/
    set L := Nat.digits n0 (n^k) with hL
    /- d is the number of digits (starting at 0)-/
    set d := L.length - 1 with hd
    have hd_natlog : d = Nat.log n0 (n^k) := by
      rw [hd, Nat.digits_len n0 (n^k) hn0_ge2 (pow_ne_zero k (ne_zero_of_lt hn)),
        Nat.add_sub_cancel]

    have hd_log : d ≤ Real.logb n0 (n^k) := by
      rw [hd_natlog]
      norm_cast
      apply nat_log_le_real_log n0 (n^k) ?_ hn0_ge2
      exact pow_pos (lt_of_succ_lt hn) k


    set L' : List ℚ := List.map Nat.cast (L.mapIdx fun i a => (a * n0 ^ i)) with hL'
    calc
    (f n)^k = f ((Nat.ofDigits n0 L : ℕ) : ℚ) := by
        rw[← map_pow, hL, Nat.ofDigits_digits n0 (n^k), ← Nat.cast_pow]
      _ = f (L'.sum) := by
        rw [Nat.ofDigits_eq_sum_mapIdx, hL']
        norm_cast
      _ ≤ (L'.map f).sum := MulRingNorm_sum_le_sum_MulRingNorm L' f
      _ ≤ (L.mapIdx fun _ _ => (n0 : ℝ)).sum := by
        simp only [hL', List.mapIdx_eq_enum_map, List.map_map]
        apply List.sum_le_sum
        rintro ⟨i,a⟩ hia
        simp only [Function.comp_apply, Function.uncurry_apply_pair]
        replace hia := List.mem_enumFrom L hia
        have ha := MulRingNorm_digit_lt_base f n0 a (n^k) hn0_ge2 hia.2.2
        push_cast
        rw [map_mul, map_pow]
        exact mul_le_of_le_of_le_one_of_nonneg (le_of_lt ha)
            (pow_le_one i (apply_nonneg f (↑ n0)) hfn0) (apply_nonneg f (↑ a))
      _ ≤ n0 * (Real.logb n0 (n ^ k) + 1) := by
        rw [List.mapIdx_eq_enum_map,
          List.eq_replicate_of_mem (a := (n0:ℝ))
            (l := List.map (Function.uncurry fun _ _ => ↑n0) (List.enum L)),
          List.sum_replicate, List.length_map, List.enum_length,
          nsmul_eq_mul, mul_comm]
        · apply mul_le_mul le_rfl ?_ (cast_nonneg (List.length L)) (cast_nonneg n0)
          apply le_add_of_le_add_right ?_ hd_log
          norm_cast
          rw [hd]
          omega
        · simp_all only [List.mem_map, Prod.exists, Function.uncurry_apply_pair, exists_and_right,
          and_imp, implies_true, forall_exists_index, forall_const]

  have hkroot : ∀ (k : ℕ) (hk: 0 < k),
      f (succ n) ≤ (↑n0 * (Real.logb (↑n0) ((succ n) ^ k) + 1))^(k:ℝ)⁻¹ := by
    intro k hk
    specialize hnk h_one_lt_succ_n hk
    have h1:  (f ↑(succ n) ^ (k:ℝ ))^(k:ℝ)⁻¹ = f ↑(succ n)  := by
      apply Real.rpow_rpow_inv (apply_nonneg f ↑(succ n))
      simp only [ne_eq, cast_eq_zero]
      exact Nat.pos_iff_ne_zero.mp hk
    rw [← h1]
    apply Real.rpow_le_rpow
    simp only [cast_succ, Real.rpow_natCast, ge_iff_le, apply_nonneg, pow_nonneg]
    exact_mod_cast hnk
    simp only [inv_nonneg, cast_nonneg]

  have h_ex_const : ∀ (k : ℕ) (hk : 0 < k),
      f (succ n) ≤ (n0 * (Real.logb (n0) (succ n) + 1)) ^ ((k:ℝ)⁻¹)* ((k)^((k:ℝ)⁻¹)) := by
    intro k hk
    apply le_trans (hkroot k hk)
    simp only [cast_succ]
    have haux (h : ℕ) : 0 ≤ n0 * (Real.logb (n0) ((n + 1)^h) + 1) := by
      apply mul_nonneg (cast_nonneg n0) (add_nonneg ?_ Real.instStrictOrderedCommRingReal.proof_3)
      apply Real.logb_nonneg (one_lt_cast.mpr hn0_ge2)
      apply one_le_pow_of_one_le
      rw [le_add_iff_nonneg_left]
      exact cast_nonneg n
    rw [← Real.mul_rpow (?_) (cast_nonneg k)]
    swap; specialize haux 1; simp only [pow_one] at haux; exact haux
    apply Real.rpow_le_rpow (haux k) ?_ (by simp only [inv_nonneg, cast_nonneg])
    rw [mul_assoc]
    apply mul_le_mul_of_nonneg_left ?_ (cast_nonneg n0)
    rw [Real.logb_pow (cast_add_one_pos n), add_mul, mul_comm]
    simp only [one_mul, add_le_add_iff_left, one_le_cast]
    exact hk

  have prod_limit :
      Filter.Tendsto (fun k : ℕ ↦ (n0 * (Real.logb (n0) (succ n) + 1)) ^ ((k:ℝ)⁻¹)* ((k)^((k:ℝ)⁻¹)))
      Filter.atTop (nhds 1) := by
    have hnlim : Filter.Tendsto (fun k : ℕ ↦ (n0 * (Real.logb (↑ n0) (succ n) + 1)) ^ ((k:ℝ)⁻¹))
        Filter.atTop (nhds 1) := one_lim_kroot_log_expr n0 (succ n) hn0_ge2 h_one_lt_succ_n
    have hprod :  Filter.Tendsto (fun k : ℕ ↦
        (n0 * (Real.logb (n0) (succ n) + 1)) ^ ((k:ℝ)⁻¹)* ((k)^((k:ℝ)⁻¹))) Filter.atTop (nhds (1*1))
            := Filter.Tendsto.mul hnlim tendsto_nat_rpow_div
    rw [mul_one] at hprod
    exact hprod

  exact forall_le_limit (f ↑(succ n))
    (fun k : ℕ ↦ (n0 * (Real.logb (↑ n0) (↑(succ n)) + 1)) ^ ((k:ℝ)⁻¹) * ((k)^((k:ℝ)⁻¹))) 1
    h_ex_const prod_limit

-- ## step 2
-- given m,n \geq 2 and |m|=m^s, |n|=n^t for s,t >0, prove t \leq s
section Step2

open Real
open BigOperators

variable (m n : ℕ) (hmge : 1 < m) (hnge : 1 < n) (notbdd: ¬ ∀(n : ℕ), f n ≤ 1)

lemma main_inequality : f n ≤ (m * (f m) / ((f m) - 1)) * ((f m) ^ (logb m n)) := by
  obtain hm := notbdd_implies_all_gt_one notbdd
  have : 1 < f m := by simp only [hm m hmge]
  let d := Nat.log m n
  have hd_length : d + 1  = (Nat.digits m (n)).length := by
    rw [Nat.digits_len m n hmge (by linarith only [hnge])]

  have h : ∀ k, 0 < k → (f n)^k ≤ ((Nat.digits m (n^k)).mapIdx fun i _ => m * (f m) ^ i).sum  := by
    intro k hk
    apply mulringnorm_n_pow_k_le_sum_digits_n0 f m hmge n hnge k hk
    intro c hc
    exact MulRingNorm_digit_lt_base f m c (n ^ k) hmge hc

  calc f ↑n ≤ ((Nat.digits m (n)).mapIdx fun i _ => m * (f m) ^ i).sum := by
        specialize h 1 zero_lt_one
        simp only [pow_one] at h
        exact h
    _ = m * ((Nat.digits m (n)).mapIdx fun i _ =>  (f m) ^ i).sum := by apply list_mul_sum
    _ = m * ((f ↑m ^ (d+1) - 1)/(f ↑m - 1)) := by
      rw [list_geom, hd_length]
      linarith only [this]
    _ ≤ m * ((f ↑m ^ (d+1))/(f ↑m - 1)) := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg m)
      exact div_le_div_of_nonneg_right (by linarith only [hmge, this]) (by linarith only [this])
    _ = ↑m * f ↑m / (f ↑m - 1) * f ↑m ^ d := by ring
    _ ≤ ↑m * f ↑m / (f ↑m - 1) * f ↑m ^ logb ↑m ↑n := by
      apply mul_le_mul_of_nonneg_left
      rw [←Real.rpow_natCast]
      apply Real.rpow_le_rpow_of_exponent_le (le_of_lt this)
      apply nat_log_le_real_log m n (by linarith [hmge]) hmge
      apply div_nonneg _ (by simp only [sub_nonneg]; exact le_of_lt this)
      exact mul_nonneg (by linarith only [hmge]) (by linarith only [this])

lemma logb_pow (k m n : ℕ) : logb m (n ^ k) = k * logb m n := by
  simp only [logb, Real.log_pow, mul_div]



lemma move_pow (A B : ℝ) (hA : 0 ≤ A) (k : ℝ) (hk : 0 < k) (hle : A ^ k ≤ B) : A ≤ B ^ (1/(k:ℝ)) := by
  have : (A ^ (k : ℝ)) ^ (1 / (k : ℝ)) = A := by
    rw [← rpow_mul, mul_one_div, div_self, rpow_one]; exact ne_of_gt hk; assumption
  rw[← this]
  refine rpow_le_rpow (rpow_nonneg hA k) hle ?_
  apply le_of_lt
  simp only [one_div, inv_pos]
  exact hk


lemma param_upperbound (k : ℕ) (hk : k ≠ 0) :
    f n ≤ (m * (f m) / ((f m) - 1)) ^ (1 / (k : ℝ)) * ((f m) ^ (logb m n)) := by
  -- the "power trick"
  have key : (f n) ^ k ≤ (m * (f m) / ((f m) - 1)) * ((f m) ^ (k * logb m n)) :=
  calc
    (f n) ^ k
    = f (↑(n ^ k)) := by simp only [map_pow, Nat.cast_pow]
    _ ≤ (m * (f m) / ((f m) - 1)) * ((f m) ^ (logb (↑ m) (↑(n ^ k)))) :=
        main_inequality m (n ^ k) hmge (one_lt_pow hnge hk ) notbdd
    _ = (m * (f m) / ((f m) - 1)) * ((f m) ^ (k * logb (↑ m) (↑(n)))) :=
      by { push_cast; rw [logb_pow]}
  obtain hm := notbdd_implies_all_gt_one notbdd
  have : 1< f m := by simp only [hm m hmge]
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


lemma ge_of_tendsto_mul' {A B : ℝ} {C : ℕ → ℝ} {limC : ℝ} {x : Filter ℕ} [Filter.NeBot x]
  (lim : Filter.Tendsto C x (nhds limC)) (h : ∀ k, A ≤ (C k) * B) : A ≤ limC * B := by
    have limCB : Filter.Tendsto (fun k ↦ (C k) * B) x (nhds (limC * B)) := by
      refine Filter.Tendsto.mul_const B lim
    refine (ge_of_tendsto' limCB h)


 lemma le_of_param_upperbound {A B C : ℝ} (hC : 0 < C) (hub : ∀ (k : ℕ), A ≤ C ^ (1 / (k:ℝ)) * B) :
     A ≤ B := by
  rw [← one_mul B]
  apply ge_of_tendsto_mul' (one_lim_of_roots C hC)
  exact hub
 -/

open Filter

lemma ge_of_tendsto_mul {A B : ℝ} {C : ℕ → ℝ} {limC : ℝ}
  (lim : Filter.Tendsto C Filter.atTop (nhds limC)) (h : ∀ k, k ≠ 0 → A ≤ (C k) * B) : A ≤ limC * B := by
  have limCB : Filter.Tendsto (fun k ↦ (C k) * B) Filter.atTop (nhds (limC * B)) := by
    refine Filter.Tendsto.mul_const B lim
  apply (ge_of_tendsto limCB )
  rw [Filter.eventually_iff_exists_mem]
  use {b | 1 ≤ b}
  constructor
  · simp only [mem_atTop_sets, ge_iff_le, Set.mem_setOf_eq]
    use 1
    exact fun b a => a
  · intro y hy
    simp only [Set.mem_setOf_eq] at hy
    exact h y (by linarith only [hy])




lemma le_of_param_upperbound {A B C : ℝ} (hC : 0 < C) (hub : ∀ (k : ℕ),k ≠ 0 →  A ≤ C ^ (1 / (k:ℝ)) * B) :
     A ≤ B := by
  let K:= fun x : ℕ  => C ^ (1 / (x : ℝ ))
  have lim : Filter.Tendsto K Filter.atTop (nhds 1) :=  one_lim_of_roots C hC
  rw [← one_mul B]
  exact ge_of_tendsto_mul lim hub


lemma key_inequality : f n ≤ (f m) ^ (logb m n) := by
  set A := m * (f m) / ((f m) - 1)

  have : f m - 1 < m * (f m) := calc
         f m - 1 < f m       := by simp only [sub_lt_self_iff, zero_lt_one]
         _       ≤ m * (f m) := le_mul_of_one_le_of_le_of_nonneg (le_of_lt (by norm_cast))
                                  (by trivial) (by simp only [apply_nonneg])

-- TODO: I proved something too strong, we actually only need 0 < A,
--       but I leave it here in case it's useful later.
  have one_lt_A : 1 < m * (f m) / ((f m) - 1) := by
    rw [one_lt_div_iff]
    left
    refine ⟨by linarith only [notbdd_implies_all_gt_one notbdd m hmge], this ⟩

  refine le_of_param_upperbound (by linarith only [one_lt_A]) ?_
  intro k hk
  exact param_upperbound m n hmge hnge notbdd k hk


lemma compare_exponents (s t : ℝ) (hm : f m = m ^ s) (hn : f n = n ^ t)  : t ≤ s := by
    have hmn : f n ≤ (f m)^(Real.logb m n) := key_inequality m n hmge hnge notbdd
    rw [← Real.rpow_le_rpow_left_iff (x:= n)]
    · rw[← hn]
      rw [hm] at hmn
      rw [← Real.rpow_mul] at hmn
      · rw [mul_comm] at hmn
        rw [Real.rpow_mul] at hmn
        · rw [Real.rpow_logb] at hmn
          · exact hmn
          · simp only [Nat.cast_pos]
            linarith only [hmge]
          · simp only [ne_eq, Nat.cast_eq_one]
            linarith only [hmge]
          · simp only [Nat.cast_pos]
            linarith only [hnge]
        · simp only [Nat.cast_nonneg]
      · simp only [Nat.cast_nonneg]
    · exact_mod_cast hnge


lemma symmetric_roles (s t : ℝ)
  (hm : f m = m ^ s) (hn : f n = n ^ t) : s = t := by
  apply le_antisymm
  refine compare_exponents _ _ hnge hmge notbdd t s hn hm
  refine compare_exponents _ _ hmge hnge notbdd s t  hm hn

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
        have fngeone : 1 < f n := notbdd_implies_all_gt_one notbdd _ oneltn
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

-- ## Non-archimedean: step 1 define `p = smallest n s. t. 0 < |p| < 1`

variable (bdd: ∀ n : ℕ, f n ≤ 1)

 /- There exists a minimal positive integer with absolute value smaller than 1 -/
lemma p_exists  (hf_nontriv : f ≠ 1) : ∃ (p : ℕ), (0 < f p ∧ f p < 1) ∧
    ∀ (m : ℕ), 0 < f m ∧ f m < 1 → p ≤ m := by
  have hn : ∃ (n : ℕ), n ≠ 0 ∧ f n ≠ 1 := by
    by_contra h
    apply hf_nontriv
    push_neg at h
    apply NormRat_eq_iff_eq_on_Nat.1
    intro n
    by_cases hn0 : n=0
    · rw [hn0]
      simp only [CharP.cast_eq_zero, map_zero]
    · push_neg at hn0
      simp only [MulRingNorm.apply_one, Nat.cast_eq_zero, hn0, ↓reduceIte]
      exact h n hn0
  obtain ⟨n,hn1,hn2⟩ := hn
  set P := {m : ℕ | 0 < f ↑m ∧ f ↑m < 1}
  have hPnonempty : Set.Nonempty P := by
    use n
    refine ⟨map_pos_of_ne_zero f (Nat.cast_ne_zero.mpr hn1), lt_of_le_of_ne (bdd n) hn2⟩
  use sInf P
  refine ⟨Nat.sInf_mem hPnonempty, ?_⟩
  intro m hm
  exact Nat.sInf_le hm
  done

section steps_2_3
-- ## Non-archimedean case: Step 2. p is prime

variable  (p : ℕ)  (hp0 : 0 < f p)  (hp1 : f p < 1)
  (hmin : ∀ (m : ℕ), 0 < f m ∧ f m < 1 → p ≤ m)

lemma one_lt_of_ne_zero_one {a : ℕ} (ne_0 : a ≠ 0) (ne_1 : a ≠ 1) : 1 < a := by
  rcases a with _ | a
  · exact (ne_0 rfl).elim
  · rw [Nat.succ_ne_succ, ← pos_iff_ne_zero] at ne_1
    exact Nat.succ_lt_succ ne_1

lemma p_is_prime : (Prime p) := by
  have neq_0 {a b : ℕ} (hab : p = a * b) : a ≠ 0 := by
    intro an0
    rw [an0] at hab
    simp at hab
    rw [hab] at hp0
    rw_mod_cast [map_zero] at hp0
    simp at hp0
  have f_positive (a b : ℕ) (hab : p = a * b) (one_lt_b : 1 < b) : 1 ≤ f a := by
    by_contra ca
    apply lt_of_not_ge at ca
    apply (@not_le_of_gt _ _ p a)
    · rw [hab]
      nth_rw 2 [← mul_one a]
      apply Nat.mul_lt_mul_of_pos_left
      · exact one_lt_b
      · simp only [pos_iff_ne_zero]
        apply neq_0 hab
    · apply hmin
      constructor
      · apply map_pos_of_ne_zero
        exact_mod_cast (neq_0 hab)
      · exact ca
  rw [← irreducible_iff_prime]
  constructor
  · simp only [Nat.isUnit_iff]
    intro p1
    rw [p1] at hp1
    simp only [Nat.cast_one, map_one, lt_self_iff_false] at hp1
  · intro a b hab
    have hba : p = b * a := by
      rw [mul_comm]
      exact hab
    simp only [Nat.isUnit_iff]
    by_contra con
    push_neg at con
    obtain ⟨a_neq_1,b_neq_1⟩ := con
    apply not_le_of_lt hp1
    rw [hab]
    simp only [Nat.cast_mul, map_mul]
    rw [← one_mul 1]
    gcongr
    · exact f_positive a b hab (one_lt_of_ne_zero_one (neq_0 hba) b_neq_1)
    · exact f_positive b a hba (one_lt_of_ne_zero_one (neq_0 hab) a_neq_1)


-- ## Step 3
/-- a natural number not divible by p has absolute value 1 -/
lemma not_divisible_norm_one (m : ℕ) (hpm : ¬ p ∣ m ) : f m = 1 := by
  have pprime : Prime (p : ℤ)  := by
    rw [← Nat.prime_iff_prime_int]
    exact Prime.nat_prime (p_is_prime p hp0 hp1 hmin)
  rw [le_antisymm_iff]
  refine ⟨bdd m, ?_ ⟩
  by_contra hm
  apply lt_of_not_le at hm
  set M := (f p) ⊔ (f m) with hM
  set k := Nat.ceil ( Real.logb  M (1/2) ) + 1 with hk
  have hcopr : IsCoprime (p ^ k : ℤ) (m ^ k) := by
    apply IsCoprime.pow
    rw [Prime.coprime_iff_not_dvd pprime]
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
  · simp only [Left.neg_pos_iff]
    apply Real.logb_neg _ hp0 hp1
    simp only [Nat.one_lt_cast]
    exact Nat.Prime.one_lt pprime
  · simp only [neg_neg]
    apply (Real.rpow_logb (by exact_mod_cast Nat.Prime.pos pprime) _ hp0).symm
    simp only [ne_eq, Nat.cast_eq_one,Nat.Prime.ne_one pprime]
    trivial



end steps_2_3
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
  obtain ⟨t,h⟩ := abs_p_eq_p_minus_t p hfp.1 hfp.2 hmin
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
