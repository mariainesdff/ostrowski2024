
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

-- ## step 1
-- if |n|>1 for some n then |n|>1 for *all* n \geq 2 (by proving contrapositive)

lemma notbdd_implies_all_gt_one (notbdd: ¬ ∀(n : ℕ), f n ≤ 1) : ∀(n : ℕ) (hn: 1 < n), f n > 1 := by
  contrapose! notbdd
  rcases notbdd with ⟨n0, hn0_ge2, hfn0⟩
  have hnk {k n : ℕ} (hk : 0 < k) (hn : 1 < n) : (f n)^k ≤ (n0 * ((Real.logb n0 n)^k  + 1)) := by
    /- L is the string of digits of `n` modulo `n0`-/
    set L := Nat.digits n0 (n^k) with hL
    /- d is the number of digits (starting at 0)-/
    set d := L.length - 1 with hd
    have hd_natlog : d = Nat.log n0 (n^k) := by
      rw [hd, Nat.digits_len _ _ hn0_ge2 (pow_ne_zero k (ne_zero_of_lt hn)), Nat.add_sub_cancel]
    have hnk : 0 ≤ ((n ^ k) :ℝ ) := by positivity
    have hd_log : d ≤ Real.logb n0 (n^k) := by sorry
      -- rw [hd_natlog, show (Nat.log n0 (n^k) : ℝ) = ((Nat.log n0 (n^k) : ℤ) : ℝ) by rfl, ← @Int.log_natCast ℝ, ← Real.floor_logb_nat_cast hn0_ge2 ?_, Nat.cast_pow]
      -- · exact Int.floor_le (Real.logb (↑n0) (↑n ^ k))
      -- · rw [← Nat.cast_pow] at hnk
      --   assumption
    have hcoeff (c : ℕ) (hc: c ∈ Nat.digits n0 (n^k)) : f c < n0 := by sorry
      -- apply lt_of_le_of_lt (MulRingNorm_nat_le_nat c f)
      -- norm_cast
      -- exact Nat.digits_lt_base hn0_ge2 hc
    calc
    (f n)^k = f ((Nat.ofDigits n0 L : ℕ) : ℚ) := by
        rw[← map_pow, hL, Nat.ofDigits_digits n0 (n^k), ← Nat.cast_pow]
      _ = f ((List.foldr (fun (x : ℕ) (y : ℕ) => x + n0 * y) 0 L : ℕ) : ℚ) := by
        rw [Nat.ofDigits_eq_foldr]; rfl
      _ ≤ List.foldr (fun (x : ℕ) (y : ℝ) => f x + f n0 * y) (f 0) L := by
        sorry
--      _ ≤ List.sum (List.mapIdx (fun (i a : ℕ) => f a * f n0 ^ i) L) := by
      _ ≤ n0 * (Real.logb n0 n ^ k + 1) := by sorry
  sorry



-- ## step 2
-- given m,n \geq 2 and |m|=m^s, |n|=n^t for s,t >0, prove t \leq s
section Step2

open Real

variable (m n : ℕ) (hmge : 1 < m) (hnge : 1 < n) (notbdd: ¬ ∀(n : ℕ), f n ≤ 1)

lemma main_inequality : f n ≤ (m * (f m) / ((f m) - 1)) * ((f m) ^ (logb m n)) := by
   sorry

lemma param_upperbound : ∀ (k : ℕ),
 f n ≤ (m * (f m) / ((f m) - 1)) ^ (1 / (k : ℝ)) * ((f m) ^ (logb m n)) := by
  intro k
  -- the "power trick"
  have easylog : logb m (n ^ k) = k * logb m n := by sorry
  have key : (f n) ^ k ≤ (m * (f m) / ((f m) - 1)) * ((f m) ^ (k * logb m n)) := calc
    (f n) ^ k = f (↑(n ^ k)) := by sorry
    _         ≤ (m * (f m) / ((f m) - 1)) * ((f m) ^ (logb (↑ m) (↑(n ^ k)))) :=
      by exact main_inequality m (n ^ k)
    _ = (m * (f m) / ((f m) - 1)) * ((f m) ^ (k * logb (↑ m) (↑(n)))) :=
      by { push_cast; rw [easylog]}
  sorry


  -- TODO: take kth root on both sides


/-- For any C > 1, the limit of C ^ (1/k) is 1 as k -> ∞. -/
lemma one_lim_of_roots (C : ℝ) (hC : 0 < C) : Filter.Tendsto
 (fun k : ℕ ↦ (C ^ (1 / (k : ℝ)))) Filter.atTop (nhds 1) := by
  rw [← Real.exp_log hC]
  simp_rw [← Real.exp_mul]
  refine Real.tendsto_exp_nhds_zero_nhds_one.comp ?_
  simp_rw [mul_one_div]
  apply tendsto_const_div_atTop_nhds_zero_nat

/-- If A ≤ (C k) * B for all k, then A ≤ limC * B, where limC is the limit of the sequence C.
-- TODO: can be generalized but we only need it here for sequences of reals.
-/
lemma ge_of_tendsto_mul' {A B : ℝ} {C : ℕ → ℝ} {limC : ℝ} {x : Filter ℕ} [Filter.NeBot x]
  (lim : Filter.Tendsto C x (nhds limC)) (h : ∀ k, A ≤ (C k) * B) : A ≤ limC * B := by
    have limCB : Filter.Tendsto (fun k ↦ (C k) * B) x (nhds (limC * B)) := by
      refine Filter.Tendsto.mul_const B lim
    refine (ge_of_tendsto' limCB h)

lemma le_of_param_upperbound {A B C : ℝ}
  (hC : 0 < C) (hub : ∀ (k : ℕ), A ≤ C ^ (1 / (k:ℝ)) * B) : A ≤ B := by
  rw [← one_mul B]
  refine ge_of_tendsto_mul' (one_lim_of_roots C hC) hub

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
  refine le_of_param_upperbound zero_lt_A ?_
  apply param_upperbound


lemma compare_exponents (s t : ℝ) (hs : 0 < s) (ht : 0 < t)
  (hm : f m = m ^ s) (hn : f n = n ^ t) : t ≤ s := sorry

end Step2

-- ## final step
-- finish the proof by symmetry (exchanging m,n and proving s \leq t) TODO

-- ## Archimedean case: end goal
/--
   If `f` is not bounded and not trivial, then it is equivalent to the usual absolute value on ℚ.
-/
theorem notbdd_implies_equiv_real (notbdd: ¬ ∀(n : ℕ), f n ≤ 1) (hf_nontriv : f ≠ 1)  : MulRingNorm.equiv f mulRingNorm_real := sorry

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

lemma b_neq_0 {a b : ℕ} (hab : p = a * b) : b ≠ 0 := by
  apply a_neq_0 hp0
  rw [mul_comm]
  exact hab

lemma a_gt_1 {a b : ℕ} (a_neq_0 : a≠ 0) (a_neq_1 : a ≠ 1) :
    1 < a := by
  rcases a with _ | a
  · exact (a_neq_0 rfl).elim
  · rw [Nat.succ_ne_succ, ← pos_iff_ne_zero] at a_neq_1
    exact Nat.succ_lt_succ a_neq_1

lemma a_lt_p {a b : ℕ} (hab : p = a * b) (b_neq_1 : b ≠ 1) : a < p := by
    rw [hab]
    nth_rw 1 [← mul_one a]
    apply Nat.mul_lt_mul_of_pos_left
    · apply b_gt_1 hab
      apply b_neq_0 hp0 hab
      exact b_neq_1
    · #check (a_gt_1 hab)
      linarith [a_gt_1 hab]

lemma fa_positive (a b : ℕ) (hab : p = a * b) : 1 ≤ f a := by
  by_contra ca
  apply lt_of_not_ge at ca
  apply not_le_of_gt (a_lt_p hab)
  apply hmin
  constructor
  · apply map_pos_of_ne_zero
    norm_cast
    exact a_neq_0 hp0 hab
  · exact ca

lemma p_is_prime : (Prime p) := by
  have a_neq_0 {a b : ℕ} (hab : p = a * b) : a ≠ 0 := by
    intro an0
    rw [an0] at hab
    simp at hab
    rw [hab] at hp0
    rw_mod_cast [map_zero] at hp0
    simp at hp0

  have fa_positive (a b : ℕ) (hab : p = a * b) : 1 ≤ f a := by
    by_contra ca
    apply lt_of_not_ge at ca

    apply not_le_of_gt

    apply hmin
    constructor
    · apply map_pos_of_ne_zero
      norm_cast
      exact a_neq_0 hp0 hab
    · exact ca


  rw [← irreducible_iff_prime]
  constructor
  · simp only [Nat.isUnit_iff]
    intro p1
    have fpIs1 : f p = 1 := by
      rw [p1]
      simp
    rw [fpIs1] at hp1
    exact (hp1 rfl).elim
  · intro a b hab
    simp only [Nat.isUnit_iff]
    by_contra con
    push_neg at con
    obtain ⟨a_neq_1,b_neq_1⟩ := con
    apply not_le_of_lt hp1
    rw [hab]
    simp only [Nat.cast_mul, map_mul]
    rw [← one_mul 1]
    gcongr






  have pneq0 : p≠ 0 := by
    intro p0
    rw [p0] at hp0
    rw_mod_cast [map_zero] at hp0
    linarith

  ·
  ·
    have aneq0: a>0 := by
      simp only [pos_iff_ne_zero]
      by_contra na
      rw [na] at hab
      simp at hab
      contradiction
    have bneq0: b>0 := by
      simp only [pos_iff_ne_zero]
      by_contra nb
      rw [nb] at hab
      simp at hab
      contradiction
    have fagr0 : f a > 0 := by
      apply map_pos_of_ne_zero
      norm_cast
      linarith
    have fbgr0 : f b > 0 := by
      apply map_pos_of_ne_zero
      norm_cast
      linarith

        have alep : a < p  := by
      rw [hab]
      nth_rw 1 [← mul_one a]
      apply Nat.mul_lt_mul_of_pos_left
      · rcases b with _ | b
        linarith
        rw [Nat.succ_ne_succ, ← pos_iff_ne_zero] at hb0
        linarith
      · exact aneq0
    have blep : b < p  := by
      rw [hab]
      nth_rw 1 [← one_mul b]
      apply Nat.mul_lt_mul_of_pos_right
      · rcases a with _ | a
        linarith
        rw [Nat.succ_ne_succ, ← pos_iff_ne_zero] at ha0
        linarith
      · exact bneq0
    have fage1 : f a ≥ 1 := by
      by_contra ca
      apply lt_of_not_ge at ca
      apply not_le_of_gt at alep
      apply alep
      apply hmin
      tauto
    have fbge1 : f b ≥ 1 := by
      by_contra cb
      apply lt_of_not_ge at cb
      apply not_le_of_gt at blep
      apply blep
      apply hmin
      tauto
    simp at fage1 fbge1


-- ## Step 3
lemma not_divisible_norm_one (m : ℕ) (hp : ¬ p ∣ m )  : f m = 1 := by
  have pnatprime : Prime p := by
    apply p_is_prime
    · exact hp0
    · exact hp1
    · exact fun m a => hmin m a
  have pprime : Prime (p : ℤ)  := by
    rw [← Nat.prime_iff_prime_int]
    exact Prime.nat_prime pnatprime
  rw [le_antisymm_iff]
  constructor
  · exact bdd m
  · by_contra cm
    apply lt_of_not_le at cm
    have copr (k : ℕ ) :  (IsCoprime (p^k : ℤ) (m^k: ℤ )) := by
      apply isCoprime_of_prime_dvd
      · intro ⟨pnot0, mnot0 ⟩
        apply pow_ne_zero k _ pnot0
        intro p0
        rw_mod_cast [p0] at hp0
        rw_mod_cast [map_zero] at hp0
        linarith
      · intro z hz zdiv
        have kneq0 : k ≠ 0 := by
          by_contra ck
          rw [ck, pow_zero] at zdiv
          apply Prime.not_dvd_one hz
          exact zdiv
        rw [Prime.dvd_pow_iff_dvd hz kneq0] at zdiv
        rw [Prime.dvd_prime_iff_associated hz pprime] at zdiv
        intro zdivmk
        rw [Prime.dvd_pow_iff_dvd hz kneq0]  at zdivmk
        rw [Int.associated_iff] at zdiv
        rcases zdiv with zp | zmp
        · rw [zp] at zdivmk
          norm_cast at zdivmk
        · rw [zmp] at zdivmk
          rw [Int.neg_dvd] at zdivmk
          norm_cast at zdivmk
    sorry






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
    apply notbdd_implies_equiv_real bdd hf_nontriv
end Rational
