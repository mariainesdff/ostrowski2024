
import Ostrowski2024.Basic
import Ostrowski2024.MulRingNormRat
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
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

-- ## auxiliary Lemmas for lists

/-Triangle inequality for absolute values applied to Lists-/
lemma flist_triang (l : List ℚ) (f : MulRingNorm ℚ) : f l.sum ≤ (l.map f).sum := by
  induction l with
  | nil => simp
  | cons head tail ih =>
    simp only [List.sum_cons, List.map_cons]
    calc f (head + List.sum tail) ≤ f head + f (List.sum tail) := by
          apply f.add_le'
      _ ≤ f head + List.sum (List.map (⇑f) tail) := by gcongr

/-Given an two integers `n n0` the absolute value of `n` raised to the `k`-th power is bounded by `n0 + n0 |n0| + n0 |n0|^2 + ...`-/
lemma mulringnorm_n_pow_k_le_sum_digits_n0 (f: MulRingNorm ℚ) (n0 : ℕ) (hn0_ge2: 1 < n0) (n : ℕ) (hn: 1 < n) (k : ℕ)
    (hk: 0 < k) (hcoeff: ∀ c ∈ Nat.digits n0 (n ^ k), f ↑c < ↑n0):
        (f n)^k ≤ ((Nat.digits n0 (n^k)).mapIdx fun i a => n0 * (f n0) ^ i).sum := by
    set L := Nat.digits n0 (n ^ k) with hL
    set L' : List ℚ := List.map Nat.cast (L.mapIdx fun i a => (a * n0 ^ i)) with hL'
    calc
    (f n)^k = f ((Nat.ofDigits n0 L : ℕ) : ℚ) := by
            rw[← map_pow, hL, Nat.ofDigits_digits n0 (n^k), ← Nat.cast_pow]
          _ = f (L'.sum) := by
            rw [Nat.ofDigits_eq_sum_mapIdx, hL']
            norm_cast
          _ ≤ (L'.map f).sum := flist_triang _ _
          _ ≤ (L.mapIdx fun i a => n0 * (f n0) ^ i).sum := by
                simp only [hL', List.mapIdx_eq_enum_map, List.map_map]
                --simp
                apply List.sum_le_sum
                rintro ⟨i,a⟩ hia
                dsimp [Function.uncurry]
                replace hia := List.mem_enumFrom _ hia
                have ha := le_of_lt (hcoeff _ hia.2.2)
                push_cast
                rw[map_mul, map_pow]
                refine mul_le_mul ha ?_ ?_ ?_
                simp
                apply pow_nonneg
                simp
                simp
open BigOperators

lemma fn_le_from_expansion (m n : ℕ) (hmge : 1 < m) (hnge : 1 < n) :
    f n ≤ m * (∑ i in Finset.range (Nat.log m n + 1), (f m)^i) := by sorry

/- ## Auxiliary lemma for limits
    If `a :ℝ` is bounded above by a function `g : ℕ → ℝ` for every `k : ℕ` then it is less or equal than the limit `lim_{k → ∞} g(k)`-/

lemma forall_le_limit (a : ℝ) (g: ℕ → ℝ) (l:ℝ) (ha: ∀ (k : ℕ),  a ≤ g k) (hg: Filter.Tendsto g Filter.atTop (nhds l) ): a ≤ l := by
  set f:= fun _ : ℕ ↦ (a : ℝ)
  have hflim : Filter.Tendsto f Filter.atTop (nhds a) := by exact tendsto_const_nhds
  exact le_of_tendsto_of_tendsto' hflim hg ha

/- For the applications we need the same statement with the extra hypothesis that ` a ≤ g(k)` holds for every `k > 0`. This is done using the notion of `eventually less`
-/
lemma forall_le_limit' (a : ℝ) (g: ℕ → ℝ) (l:ℝ) (ha: ∀ (k : ℕ) (_ : 0 < k), a ≤ g k)
  (hg: Filter.Tendsto g Filter.atTop (nhds l) ): a ≤ l := by
  set f:= fun _ : ℕ ↦ (a : ℝ) with hf
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
lemma one_lim_kroot_log_expr (n0 n : ℕ) (hn0_ge2: 1 < n0) (hn : 1 < n) : Filter.Tendsto (fun k : ℕ ↦ (n0 * (Real.logb (↑ n0) (↑n) + 1)) ^ ((k:ℝ)⁻¹)) Filter.atTop (nhds 1) := by
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

/-auxiliary lemma to compute the limit as `k → ∞` of the function `k : ℕ ↦ k^k`-/
lemma bar : Filter.Tendsto (fun x : ℝ  ↦ ( x ^ (x)⁻¹)) Filter.atTop (nhds 1) → Filter.Tendsto (fun k : ℕ ↦ ((k:ℝ) ^ ((k:ℝ)⁻¹))) Filter.atTop (nhds 1) := by
  rw [Filter.tendsto_def,Filter.tendsto_def]
  simp only [Filter.mem_atTop_sets, ge_iff_le, Set.mem_preimage]
  intro h s1 hs1
  rcases (h s1 hs1) with ⟨s2, hs2⟩

  use (Nat.floor s2)+1
  intro b hs2b
  specialize hs2 b
  have : s2 ≤ ↑b := by
    calc s2 ≤ ⌊s2⌋₊ + 1 := le_of_lt (Nat.lt_floor_add_one s2)
      _ ≤ ↑b := by exact_mod_cast hs2b
  exact hs2 this

/-extends the lemma `tendsto_rpow_div` when the function has natural input-/
lemma tendsto_nat_rpow_div : Filter.Tendsto (fun k : ℕ ↦ ((k:ℝ) ^ ((k:ℝ)⁻¹))) Filter.atTop (nhds 1) := by
  apply bar
  convert_to Filter.Tendsto (fun x : ℝ ↦ (x ^ (1/x))) Filter.atTop (nhds 1)
  · simp only [one_div]
  apply tendsto_rpow_div

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
    linarith [hn0]
    simp only [ne_eq, Nat.cast_eq_one]
    linarith [hn0]
    exact_mod_cast hn
  have : n0 ^ (Nat.log n0 n) ≤ (n0 : ℝ)^(Real.logb n0 n ) := by
    rw [hreal]
    exact_mod_cast hnat
  have hn0_gt1R : 1 < (n0:ℝ) := by exact_mod_cast hn0
  rw [← Real.rpow_le_rpow_left_iff hn0_gt1R]
  exact_mod_cast this

/-
The lemma formalizes taking the `k`-th root in the inequality `f ↑n ^ k ≤ ↑n0 * (Real.logb (↑n0) (↑n ^ k) + 1)`-/
lemma fn_le_kroot_log (n0 : ℕ) (hn0 : 1 < n0) (hnk : ∀ {n : ℕ}, 1 < n → ∀ {k : ℕ}, 0 < k → f ↑n ^ k ≤ ↑n0 * (Real.logb (↑n0) (↑n ^ k) + 1)): ∀ (n : ℕ) (hn : 1 < n) (k : ℕ) (hk: 0 < k), f ↑n ≤ (↑n0 * (Real.logb (↑n0) (↑n ^ k) + 1))^(k:ℝ)⁻¹ := by
      --intro n0
      intro n hn k hk
      -- have hnk_pos : 1 < (↑n ^ k) := by
      --   apply one_lt_pow hn
      --   linarith
      -- have hlog_pos : 0 < (Real.logb (↑n0) (↑n ^ k)) := by
      --   refine Real.logb_pos ?_ ?_
      --   · norm_cast
      --   · norm_cast
      replace hnk : (f ↑n ^ k) ^ (k:ℝ)⁻¹ ≤ (↑n0 * (Real.logb (↑n0) (↑n ^ k) + 1))^(k:ℝ)⁻¹ := by
        apply @Real.rpow_le_rpow _ _ (k:ℝ)⁻¹
        · apply pow_nonneg
          exact apply_nonneg f _
        · apply hnk hn hk
        · apply le_of_lt
          positivity
      have : (f ↑n ^ (k:ℝ)) ^ (k:ℝ)⁻¹ = f ↑n := by
        --norm_cast
        apply Real.rpow_rpow_inv
        · exact apply_nonneg f _
        · simp
          omega
      rw [← this]
      convert hnk
      rw [Real.rpow_nat_cast]

/- intermediate lemma computing upper bound of `f ↑ n` in terms of `k`-th root of logarithm -/
  lemma fn_le_mul_kroot (f: MulRingNorm ℚ) (n0 : ℕ) (hn0 : 1 < n0) : ∀ (n : ℕ) (hn : 1 < n) (k : ℕ) (hk: 0 < k) (hkroot : f ↑n ≤ (↑n0 * (Real.logb (↑n0) (↑n ^ k) + 1))^(k:ℝ)⁻¹), f ↑ n ≤ (n0 * (Real.logb (↑ n0) (↑n) + 1)) ^ ((k:ℝ)⁻¹)* ((k)^((k:ℝ)⁻¹)) := by
    -- intro n0
    intro n hn k hk hkroot
   -- replace hkroot := hkroot n hn k hk
    rw [← Real.mul_rpow]
    · rw [mul_add,add_mul]
      simp only [mul_one, ge_iff_le]
      rw [mul_assoc]
      apply le_trans hkroot
      rw_mod_cast [Real.rpow_le_rpow_iff]
      · push_cast
        rw_mod_cast [mul_add]
        apply add_le_add
        · simp only [Nat.cast_pow]
          apply mul_le_mul
          · simp only [le_refl]
          · rw [← Real.log_div_log]
            rw [← Real.log_div_log]
            rw [mul_comm]
            rw [mul_div]
            rw [← Real.log_rpow]
            · apply div_le_div
              · apply Real.log_nonneg
                apply Real.one_le_rpow
                · norm_cast
                  linarith
                · norm_cast
                  linarith
              · simp
              · apply Real.log_pos
                norm_cast
              · simp
            · norm_cast
              linarith
          · apply Real.logb_nonneg
            · norm_cast
            · norm_cast
              apply Nat.one_le_pow
              linarith
          · norm_cast
            linarith
        · simp only [mul_one, Nat.cast_mul]
          norm_cast
          apply Nat.le_mul_of_pos_right _ hk
      · apply mul_nonneg
        · norm_cast
          linarith
        · apply add_nonneg
          · apply Real.logb_nonneg
            · norm_cast
            · norm_cast
              apply Nat.one_le_pow
              linarith
          · simp
      · norm_cast
        simp
        apply add_nonneg
        · apply mul_nonneg
          · norm_cast
            linarith
          · rw [← zero_mul 0]
            gcongr
            apply mul_nonneg
            · apply Real.log_nonneg
              norm_cast
              linarith
            · rw [inv_nonneg]
              apply Real.log_nonneg
              norm_cast
              linarith
            · apply Real.logb_nonneg
              · norm_cast
              · norm_cast
                linarith
            · norm_cast
              linarith
        · apply mul_nonneg
          · norm_cast
            linarith
          · norm_cast
            linarith
      · simp only [inv_pos, Nat.cast_pos, hk]
    · apply mul_nonneg
      · norm_cast
        linarith
      · apply add_nonneg
        · apply Real.logb_nonneg
          · norm_cast
          · norm_cast
            linarith
        · simp
    · norm_cast
      simp only [zero_le]

  /- set d := Nat.log m n with hd
  have hnmd : f n ≤ m * (∑ i in Finset.range (d + 1), (f m)^i) := by sorry -/
open BigOperators






lemma notbdd_implies_all_gt_one (notbdd: ¬ ∀(n : ℕ), f n ≤ 1) : ∀(n : ℕ) (hn: 1 < n), f n > 1 := by
  contrapose! notbdd
  rcases notbdd with ⟨n0, hn0_ge2, hfn0⟩
  have hnk {n : ℕ} (hn : 1 < n) {k : ℕ} (hk : 0 < k)  : (f n)^k ≤ (n0 * (Real.logb n0 (n^k)  + 1)) := by
    /- L is the string of digits of `n` modulo `n0`-/
    set L := Nat.digits n0 (n^k) with hL
    /- d is the number of digits (starting at 0)-/
    set d := L.length - 1 with hd
    have hd_natlog : d = Nat.log n0 (n^k) := by
      rw [hd, Nat.digits_len _ _ hn0_ge2 (pow_ne_zero k (ne_zero_of_lt hn)), Nat.add_sub_cancel]
    have hnk : 0 ≤ ((n ^ k) :ℝ ) := by positivity
    have hnknz : n^k ≠ 0 := by
      simp only [ne_eq, pow_eq_zero_iff', not_and, not_not]
      intro h
      linarith [h,hn]
    have hd_log : d ≤ Real.logb n0 (n^k) := by
      rw [hd_natlog]
      norm_cast
      apply nat_log_le_real_log n0 (n^k) ?_ hn0_ge2
      omega
    have hcoeff (c : ℕ) (hc: c ∈ Nat.digits n0 (n^k)) : f c < n0 := by
      have hcltn0 : c < n0 := Nat.digits_lt_base hn0_ge2 hc
      have := MulRingNorm_nat_le_nat c f
      apply lt_of_le_of_lt
      · exact this
      · exact_mod_cast hcltn0
    set L' : List ℚ := List.map Nat.cast (L.mapIdx fun i a => (a * n0 ^ i)) with hL'
    calc
    (f n)^k = f ((Nat.ofDigits n0 L : ℕ) : ℚ) := by
        rw[← map_pow, hL, Nat.ofDigits_digits n0 (n^k), ← Nat.cast_pow]
      _ = f (L'.sum) := by
        rw [Nat.ofDigits_eq_sum_mapIdx, hL']
        norm_cast
      _ ≤ (L'.map f).sum := flist_triang _ _
      _ ≤ (L.mapIdx fun i a => (n0 : ℝ)).sum := by
        simp only [hL', List.mapIdx_eq_enum_map, List.map_map]
        apply List.sum_le_sum
        rintro ⟨i,a⟩ hia
        dsimp [Function.uncurry]
        replace hia := List.mem_enumFrom _ hia
        have ha := hcoeff _ hia.2.2
        push_cast
        rw[map_mul, map_pow]
        calc f a * f n0 ^ i ≤ n0 * 1 := by
              refine mul_le_mul ha.le ?_ ?_ ?_
              · apply pow_le_one _ _ hfn0
                · exact apply_nonneg f _
              · apply pow_nonneg
                exact apply_nonneg f _
              · linarith
          _ = n0 := mul_one _
      _ ≤ n0 * (Real.logb n0 (n ^ k) + 1) := by
        rw [List.mapIdx_eq_enum_map,
          List.eq_replicate_of_mem (a := (n0:ℝ))
            (l := List.map (Function.uncurry fun i a => ↑n0) (List.enum L)),
          List.sum_replicate, List.length_map, List.enum_length,
          nsmul_eq_mul, mul_comm]
        refine mul_le_mul le_rfl ?_ ?_ ?_
        · calc ↑(List.length L) ≤ ↑d + 1 := by
                rw [hd]
                norm_cast
                omega
               _ ≤ Real.logb (↑n0) (↑n ^ k) + 1 := by
                simp
                exact hd_log
        · simp
        · simp
        · simp_all
  have hkroot : ∀ (n : ℕ) (hn : 1 < n) (k : ℕ) (hk: 0 < k), f ↑n ≤ (↑n0 * (Real.logb (↑n0) (↑n ^ k) + 1))^(k:ℝ)⁻¹ := fn_le_kroot_log n0 hn0_ge2 hnk

  have  h_ex_const : ∀ (n : ℕ) (hn : 1 < n) (k : ℕ) (hk: 0 < k), f ↑ n ≤ (n0 * (Real.logb (↑ n0) (↑n) + 1)) ^ ((k:ℝ)⁻¹)* ((k)^((k:ℝ)⁻¹)) := by
    intro n hn k hk
    apply fn_le_mul_kroot f n0 hn0_ge2
    · exact hn
    · exact hk
    · exact hkroot n hn k hk

  have prod_limit : ∀ (n : ℕ), 1 < n → Filter.Tendsto (fun k : ℕ ↦ (n0 * (Real.logb (↑ n0) (↑n) + 1)) ^ ((k:ℝ)⁻¹)* ((k)^((k:ℝ)⁻¹))) Filter.atTop (nhds 1) := by
    intro n hn
    have hnlim : Filter.Tendsto (fun k : ℕ ↦ (n0 * (Real.logb (↑ n0) (↑n) + 1)) ^ ((k:ℝ)⁻¹))
        Filter.atTop (nhds 1) := one_lim_kroot_log_expr n0 n hn0_ge2 hn

    have hprod :  Filter.Tendsto (fun k : ℕ ↦
        (n0 * (Real.logb (↑ n0) (↑n) + 1)) ^ ((k:ℝ)⁻¹)* ((k)^((k:ℝ)⁻¹))) Filter.atTop (nhds (1*1))
            := Filter.Tendsto.mul hnlim tendsto_nat_rpow_div
    simp at hprod
    exact hprod

  intro n
  cases' n with n
  · norm_cast
    rw [map_zero]
    simp
  · by_cases hn : n = 0
    norm_cast
    simp[hn]
    · have hn_ge_one : 1 < Nat.succ n := by omega
      specialize h_ex_const (Nat.succ n) hn_ge_one
      specialize prod_limit (Nat.succ n) hn_ge_one
      refine' forall_le_limit' (f ↑(Nat.succ n))
        (fun k : ℕ ↦ (n0 * (Real.logb (↑ n0) (↑(Nat.succ n)) + 1)) ^ ((k:ℝ)⁻¹)* ((k)^((k:ℝ)⁻¹))) 1
        h_ex_const prod_limit

-- ## step 2
-- given m,n \geq 2 and |m|=m^s, |n|=n^t for s,t >0, prove t \leq s
section Step2

open Real
open BigOperators

variable (m n : ℕ) (hmge : 1 < m) (hnge : 1 < n) (notbdd: ¬ ∀(n : ℕ), f n ≤ 1)

lemma main_inequality : f n ≤ (m * (f m) / ((f m) - 1)) * ((f m) ^ (logb m n)) := by
  obtain hm := notbdd_implies_all_gt_one notbdd
  have : 1< f m := by simp only [hm m hmge]
  let d := Nat.log m n
  have hsum : ∑ i in Finset.range (d + 1), f ↑m ^ i = (f ↑m ^ (d+1) - 1)/(f ↑m - 1) := by
    rw [geom_sum_eq]
    apply ne_of_gt
    linarith
  calc f ↑n ≤ m * (∑ i in Finset.range (d + 1), (f m)^i) :=  fn_le_from_expansion m n hmge hnge
    _ = m * (f ↑m ^ (d+1) - 1)/(f ↑m - 1) := by rw [hsum]; ring
    _ ≤ m * (f ↑m ^ (d+1))/(f ↑m - 1) := by
      apply div_le_div_of_nonneg_right (by linarith only [hmge, this]) (by linarith only [this])
    _ = ↑m * f ↑m / (f ↑m - 1) * f ↑m ^ d := by ring
    _ ≤ ↑m * f ↑m / (f ↑m - 1) * f ↑m ^ logb ↑m ↑n := by
      apply mul_le_mul_of_nonneg_left
      rw [←Real.rpow_nat_cast]
      apply Real.rpow_le_rpow_of_exponent_le (le_of_lt this)
      apply nat_log_le_real_log m n (by linarith [hmge]) hmge
      apply div_nonneg _ (by simp only [sub_nonneg]; exact le_of_lt this)
      exact mul_nonneg (by linarith only [hmge]) (by linarith only [this])



lemma logb_pow (k m n : ℕ) : logb m (n ^ k) = k * logb m n := by
  simp only [logb, log_pow, mul_div]



lemma move_pow (A B : ℝ) (hA : 0 ≤ A) (k : ℝ) (hk : 0 < k) (hle : A ^ k ≤ B) : A ≤ B ^ (1/(k:ℝ)) := by
  have : (A ^ (k : ℝ)) ^ (1 / (k : ℝ)) = A := by
    rw [← rpow_mul, mul_one_div, div_self, rpow_one]; exact ne_of_gt hk; assumption
  rw[← this]
  refine rpow_le_rpow (rpow_nonneg hA k) hle ?_
  apply le_of_lt
  simp only [one_div, inv_pos]
  assumption


lemma param_upperbound (k : ℕ) (hk : k ≠ 0) : f n ≤ (m * (f m) / ((f m) - 1)) ^ (1 / (k : ℝ)) * ((f m) ^ (logb m n)) := by
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
    · rw [← rpow_mul, triviality,rpow_nat_cast, rpow_one]
      exact key
      exact our_prod_nonneg
    · apply rpow_nonneg
      exact our_prod_nonneg
    · simp only [Nat.cast_pos.2 (Nat.pos_of_ne_zero hk)]
    · exact (apply_nonneg f ↑n)




/-- If A ≤ (C k) * B for all k, then A ≤ limC * B, where limC is the limit of the sequence C.
-- TODO: can be generalized but we only need it here for sequences of reals.
-/
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

open Filter
lemma ge_of_tendsto_mul'' {A B : ℝ} {C : ℕ → ℝ} {limC : ℝ}
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
    exact h y (by linarith)


/- open Filter
lemma ge_of_tendsto_mul'' {A B : ℝ} {K : ℕ → ℝ}
  (lim : Filter.Tendsto K Filter.atTop (nhds 1)) (h : ∀ k, k≠ 0 →  A ≤ (K k) * B) : A ≤ B := by
  by_cases hB : B > 0
  · have : A/B ≤ 1 := by sorry

    sorry

  · push_neg at hB
    rw [hB]
    rw [hB] at h
    specialize h 1 one_ne_zero
    simp only [mul_zero] at h
    exact h -/

lemma le_of_param_upperbound' {A B C : ℝ} (hC : 0 < C) (hub : ∀ (k : ℕ),k ≠ 0 →  A ≤ C ^ (1 / (k:ℝ)) * B) :
     A ≤ B := by
  let K:= fun x : ℕ  => C ^ (1 / (x : ℝ ))
  have lim : Filter.Tendsto K Filter.atTop (nhds 1) :=  one_lim_of_roots C hC
  rw [← one_mul B]
  exact ge_of_tendsto_mul'' lim hub


lemma key_inequality : f n ≤ (f m) ^ (logb m n) := by
  set A := m * (f m) / ((f m) - 1)

  have : f m - 1 < m * (f m) := calc
         f m - 1 < f m       := by linarith
         _       ≤ m * (f m) := le_mul_of_one_le_of_le_of_nonneg (le_of_lt (by norm_cast))
                                  (by trivial) (by simp only [apply_nonneg])

-- TODO: I proved something too strong, we actually only need 0 < A,
--       but I leave it here in case it's useful later.
  have one_lt_A : 1 < m * (f m) / ((f m) - 1) := by
    rw [one_lt_div_iff]
    left
    constructor
    · linarith [notbdd_implies_all_gt_one notbdd m hmge]
    · linarith

  have zero_lt_A : 0 < A := by linarith
  refine le_of_param_upperbound' zero_lt_A ?_
  intro k hk
  apply param_upperbound m n hmge hnge notbdd k hk


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
            linarith
          · simp only [ne_eq, Nat.cast_eq_one]
            linarith
          · simp only [Nat.cast_pos]
            linarith
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



theorem notbdd_implies_equiv_real (notbdd: ¬ ∀(n : ℕ), f n ≤ 1)  : MulRingNorm.equiv f mulRingNorm_real := by
  obtain ⟨m, hm⟩ := Classical.exists_not_of_not_forall notbdd
  have oneltm : 1<m := by
    by_contra!
    replace this : m = 0 ∨ m = 1 := by omega
    rcases this with (rfl | rfl )
    · rw_mod_cast [map_zero] at hm
      simp at hm
    · rw_mod_cast [map_one] at hm
      simp at hm
  set s := Real.logb m (f m) with hs
  use s⁻¹
  constructor
  · rw [hs]
    simp
    apply Real.logb_pos
    · simp
      exact oneltm
    · linarith
  · rw_mod_cast [← Norm_Rat_equiv_iff_equiv_on_Nat']
    intro n
    have onelefn : n>1 → 1 < f n := by
      apply notbdd_implies_all_gt_one notbdd n
    by_cases nzero : n=0
    · rw_mod_cast [nzero]
      simp only [CharP.cast_eq_zero, map_zero, le_refl]
      rw [Real.rpow_eq_zero]
      · simp only [le_refl]
      · simp only [ne_eq, inv_eq_zero]
        rw [hs]
        simp only [Real.logb_eq_zero, Nat.cast_eq_zero, Nat.cast_eq_one, map_eq_zero]
        norm_cast
        simp only [Int.reduceNegSucc, Int.cast_neg, Int.cast_one, false_or]
        push_neg
        constructor
        · omega
        · constructor
          · omega
          · constructor
            · omega
            · constructor
              · linarith
              · linarith
    · by_cases none : n=1
      · rw [none]
        simp only [Nat.cast_one, map_one, Real.one_rpow]
      · have oneltn : 1<n := by
          omega
        have fngeone : f n > 1 := by
          apply notbdd_implies_all_gt_one notbdd
          exact oneltn
        set t := Real.logb n (f n) with ht
        have hm' : (f m )= m ^ s := by
          rw [hs,Real.rpow_logb ]
          · norm_cast
            omega
          · norm_cast
            omega
          · linarith
        have hn : (f n )= n ^ t := by
          rw [ht,Real.rpow_logb ]
          · norm_cast
            omega
          · norm_cast
          · linarith
        have seqt : s = t := by
          apply symmetric_roles
          · exact oneltm
          · exact oneltn
          · exact notbdd
          · exact hm'
          · exact hn
        rw [seqt,hn]
        simp only [Nat.cast_nonneg, mul_ring_norm_eq_abs, Nat.abs_cast, Rat.cast_natCast]
        rw [← Real.rpow_mul]
        · convert Real.rpow_one _
          apply mul_inv_cancel
          rw [ht]
          apply Real.logb_ne_zero_of_pos_of_ne_one
          · assumption_mod_cast
          · positivity
          · linarith
        · linarith


    /-
    have hms : (m : ℝ) ^ s = f m := by
      rw [hs]
    -- ↑m ^ Real.logb (↑m) (f ↑m) = ↑m
    sorry

    simp only [mul_ring_norm_eq_abs, Rat.cast_abs]
    sorry -/


end Archimedean

section Nonarchimedean

-- ## Non-archimedean: step 1 define `p = smallest n s. t. 0 < |p| < 1`

variable (bdd: ∀ n : ℕ, f n ≤ 1)

lemma p_exists  (hf_nontriv : f ≠ 1) : ∃ (p : ℕ), (0 < f p ∧ f p < 1) ∧ ∀ (m : ℕ), 0 < f m ∧ f m < 1 → p ≤ m := by
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
  have hnlt1 : f n < 1 := by
    exact lt_of_le_of_ne (bdd n) hn2
  have hngt0 : 0 < f n := by
    apply map_pos_of_ne_zero
    exact Nat.cast_ne_zero.mpr hn1
  set P := {m : ℕ | 0 < f ↑m ∧ f ↑m < 1}
  have hPnonempty : Set.Nonempty P := by
    use n
    refine ⟨hngt0,hnlt1 ⟩
  use sInf P
  refine ⟨Nat.sInf_mem hPnonempty,?_⟩
  intro m hm
  exact Nat.sInf_le hm
  done

section steps_2_3
-- ## Non-archimedean case: Step 2. p is prime

variable  (p : ℕ)  (hp0 : 0 < f p)  (hp1 : f p < 1)
  (hmin : ∀ (m : ℕ), 0 < f m ∧ f m < 1 → p ≤ m)

lemma ne01_gt_1 {a : ℕ} (ne_0 : a≠ 0) (ne_1 : a ≠ 1) :
    1 < a := by
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
    simp at hp1
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
    · exact f_positive a b hab (ne01_gt_1 (neq_0 hba) b_neq_1)
    · exact f_positive b a hba (ne01_gt_1 (neq_0 hab) a_neq_1)


-- ## Step 3

lemma not_divisible_norm_one (m : ℕ) (hpm : ¬ p ∣ m )  : f m = 1 := by
  have pprime : Prime (p : ℤ)  := by
    rw [← Nat.prime_iff_prime_int]
    exact Prime.nat_prime (p_is_prime _ hp0 hp1 hmin)
  rw [le_antisymm_iff]
  set M := (f p) ⊔ (f m) with hM
  set k0 := Nat.ceil ( Real.logb  M (1/2) )+1 with hk
  have copr : IsCoprime (p^k0 : ℤ) (m^k0) := by
    apply IsCoprime.pow
    rw [Prime.coprime_iff_not_dvd pprime]
    exact_mod_cast hpm
  obtain ⟨a,b,bezout⟩ := copr
  constructor
  · exact bdd m
  · by_contra hm
    apply lt_of_not_le at hm

    have le_half x (hx0 : 0 < x) (hx1 : x < 1) (hxM : x ≤ M) :
      x^k0 < 1/2 := by calc
        x ^ k0 = x ^ (k0:ℝ) := by norm_cast
        _ < x ^ Real.logb M (1 / 2) := by
          apply Real.rpow_lt_rpow_of_exponent_gt hx0 hx1
          rw [hk]
          calc
            Real.logb M (1 / 2) ≤ (Nat.ceil  (Real.logb  M (1/2)) :ℝ) := by
              exact Nat.le_ceil (Real.logb M (1/2))
            _ < ↑(⌈Real.logb M (1 / 2)⌉₊ + 1) := by
              norm_cast
              apply lt_add_one
        _ ≤ x ^ (Real.logb x) (1/2) := by
          apply Real.rpow_le_rpow_of_exponent_ge hx0
          · linarith only [hx1]
          · simp only [← Real.log_div_log]
            ring_nf
            simp only [one_div, Real.log_inv, neg_mul, neg_le_neg_iff]
            rw [mul_le_mul_left]
            · rw [inv_le_inv_of_neg]
              · apply Real.log_le_log hx0 hxM
              · rw [Real.log_neg_iff]
                · rw [hM]
                  rw [sup_lt_iff]
                  constructor
                  · exact hp1
                  · exact hm
                · rw [hM]
                  rw [lt_sup_iff]
                  left
                  exact hp0
              · rw [Real.log_neg_iff hx0]
                exact hx1
            · apply Real.log_pos
              exact one_lt_two
        _ = 1/2 := by
          rw [Real.rpow_logb hx0]
          · linarith
          · simp only [one_div, inv_pos, Nat.ofNat_pos]

    apply lt_irrefl (1 : ℝ)
    calc
      (1:ℝ) = f 1 := by rw [map_one]
      _ = f (a * p ^ k0 + b * m ^ k0) := by
        rw_mod_cast [bezout]
        norm_cast
      _ ≤ f (a * p ^ k0) + f (b * m ^ k0) := by apply f.add_le'
      _ ≤ 1 * (f p) ^ k0 + 1 * (f m) ^ k0 := by
        simp only [map_mul, map_pow, le_refl]
        gcongr
        all_goals rw [← f_of_abs_eq_f]; apply bdd
      _ = (f p) ^ k0 + (f m) ^ k0 := by simp
      _ < 1 := by
        rw [← add_halves (a:=1)]
        apply add_lt_add
        · apply le_half _ hp0 hp1
          rw [hM]
          simp only [le_sup_left]
        · apply le_half (f m) _ hm
          · rw [hM]
            simp only [le_sup_right]
          · apply map_pos_of_ne_zero
            intro m0
            apply hpm
            rw_mod_cast [m0]
            simp

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
    apply (Real.rpow_logb _ _ hp0).symm
    exact_mod_cast Nat.Prime.pos pprime
    simp only [ne_eq, Nat.cast_eq_one,Nat.Prime.ne_one pprime]
    trivial



end steps_2_3
-- ## Non-archimedean case: end goal
/--
  If `f` is bounded and not trivial, then it is equivalent to a p-adic absolute value.
-/
theorem bdd_implies_equiv_padic (bdd: ∀ n : ℕ, f n ≤ 1) (hf_nontriv : f ≠ 1) :
∃ p, ∃ (hp : Fact (Nat.Prime p)), MulRingNorm.equiv f (mulRingNorm_padic p) :=
  by
  obtain ⟨p,hfp,hmin⟩ := p_exists bdd hf_nontriv
  have hprime : Prime p := p_is_prime p hfp.1 hfp.2 hmin
  use p
  have hp : Fact (Nat.Prime p) := by
    rw [fact_iff]
    exact Prime.nat_prime hprime
  use hp
  obtain ⟨t,h⟩ := abs_p_eq_p_minus_t p hfp.1 hfp.2 hmin
  use (t⁻¹)
  have tnezero : t ≠ 0 := by linarith [h.1]
  have oneovertnezero : t⁻¹ ≠ 0 := by
    simp only [ne_eq, inv_eq_zero]
    linarith [h.1]
  constructor
  · simp only [one_div, inv_pos, h.1]
  · ext x
    apply (Norm_Rat_equiv_iff_equiv_on_Nat t).1
    intro n
    by_cases hn : n=0
    · rw [hn]
      simp only [CharP.cast_eq_zero, map_zero, ne_eq, oneovertnezero, not_false_eq_true,
        Real.zero_rpow]
    · push_neg at hn
      rcases Nat.exists_eq_pow_mul_and_not_dvd hn p (Nat.Prime.ne_one (Prime.nat_prime hprime)) with ⟨ e, m, hpm, hnpm⟩
      rw [hnpm]
      simp only [Nat.cast_mul, Nat.cast_pow, map_mul, map_pow, mul_ring_norm_eq_padic_norm,
        padicNorm.padicNorm_p_of_prime, Rat.cast_inv, Rat.cast_natCast, inv_pow]
      rw [not_divisible_norm_one bdd p hfp.1 hfp.2 hmin m hpm]
      rw [←padicNorm.nat_eq_one_iff] at hpm
      rw [hpm,h.2]
      simp only [mul_one, Rat.cast_one]
      rw [← Real.rpow_natCast_mul]
      swap; apply (Real.rpow_nonneg (Nat.cast_nonneg p))
      rw [← Real.rpow_mul (Nat.cast_nonneg p), mul_comm ↑e t⁻¹, ← mul_assoc]
      simp only [neg_mul]
      rw [Real.instLinearOrderedFieldReal.proof_10 t tnezero]
      simp only [one_mul]
      rw [Real.rpow_neg]
      simp only [Real.rpow_nat_cast]
      exact Nat.cast_nonneg p
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
