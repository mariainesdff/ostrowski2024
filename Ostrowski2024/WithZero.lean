import Mathlib.Data.Int.WithZero
import Mathlib


--#min_imports

noncomputable section

open scoped  NNReal

open Multiplicative WithZero Equiv WithZeroMulInt

variable {R : Type*} [LinearOrderedRing R] {a : R} {n : ℕ}

lemma pow_eq_one_of (ha1 : a ≠ 1) (ha2 : a ≠ - 1) (hexp : a ^ n = 1) : n = 0 := by
  cases' pow_eq_one_iff_cases.mp hexp with h h
  exact h
  cases' h with h h
  exact False.elim (ha1 h)
  simp_all only [ne_eq, neg_eq_zero, one_ne_zero, not_false_eq_true, not_true_eq_false]

lemma foo {e : ℝ} {n : ℤ} (he0 : 0 < e) (he1 : e ≠ 1) (hexp : e ^ n = 1) : n = 0 := by
  cases' Int.natAbs_eq n with h h
  all_goals rw [h] at hexp
  · norm_cast at hexp
    exact Int.natAbs_eq_zero.mp <| pow_eq_one_of he1 (by linarith) hexp
  · simp only [@zpow_neg, inv_eq_one] at hexp
    norm_cast at hexp
    exact Int.natAbs_eq_zero.mp <| pow_eq_one_of he1 (by linarith) hexp

theorem eq_one {e : NNReal} {m : ℤₘ₀} (he0 : e ≠ 0) (he1 : e ≠ 1) (hm : m ≠ 0) : toNNReal he0 m = 1 ↔ m = 1 := by
  constructor
  · rw [toNNReal_neg_apply he0 hm]
    intro h
    have h1 : (e : ℝ) ^ toAdd (unzero hm) = 1 := by norm_cast
    have := foo (mod_cast pos_iff_ne_zero.mpr he0) (by norm_cast) h1
    have h4 : ((1 : Multiplicative ℤ) : ℤₘ₀) ≠ 0 := Ne.symm (zero_ne_one' ℤₘ₀)
    rw [toAdd_eq_zero, ← WithZero.unzero_coe h4] at this
    rw [← WithZero.coe_unzero hm, this]
    simp_all only [ne_eq, coe_one, unzero_coe, coe_one, ne_eq, one_ne_zero, not_false_eq_true]
    rfl
  · intro a
    subst a
    simp_all only [ne_eq, one_ne_zero, not_false_eq_true, map_one]

theorem lt_one {e : NNReal} {m : ℤₘ₀} (he1 : 1 < e) (hm : m ≠ 0) : toNNReal (ne_zero_of_lt he1) m < 1 ↔ m < 1 := by
  have mono := toNNReal_strictMono he1
  unfold StrictMono at mono
  have : 1 = (toNNReal (ne_zero_of_lt he1)) 1 := rfl
  simp_rw [this]
  constructor
  · contrapose!
    intro h
    exact (StrictMono.le_iff_le mono).mpr h
  · intro h
    exact mono h

theorem le_one {e : NNReal} {m : ℤₘ₀} (he1 : 1 < e) (hm : m ≠ 0) : toNNReal (ne_zero_of_lt he1) m ≤ 1 ↔ m ≤ 1 := by
  have mono := toNNReal_strictMono he1
  constructor
  · apply le_imp_le_of_lt_imp_lt
    exact fun a => LT.lt.trans_eq' (mono a) rfl
  · apply le_imp_le_of_lt_imp_lt
    intro h
    exact (StrictMono.lt_iff_lt mono).mp h

#exit

section LinearOrderedField
variable {R : Type*} [LinearOrderedField R] {a b : R} {n : ℤ}

lemma zpow_eq_zpow_iff_of_ne_zero (hn : n ≠ 0) : a ^ n = b ^ n ↔ a = b ∨ a = -b ∧ Even n :=
  sorry
  /- match n.even_xor_odd with
  | .inl hne => by simp only [*, and_true, ← abs_eq_abs,
    ← pow_left_inj (abs_nonneg a) (abs_nonneg b) hn, hne.1.pow_abs]
  | .inr hn => by simp [hn, (hn.1.strictMono_pow (R := R)).injective.eq_iff] -/

lemma zpow_eq_zpow_iff_cases : a ^ n = b ^ n ↔ n = 0 ∨ a = b ∨ a = -b ∧ Even n := by
  rcases eq_or_ne n 0 with rfl | hn <;> simp [pow_eq_pow_iff_of_ne_zero, *]

lemma pow_eq_one_iff_of_ne_zero (hn : n ≠ 0) : a ^ n = 1 ↔ a = 1 ∨ a = -1 ∧ Even n := by
  simp [← pow_eq_pow_iff_of_ne_zero hn]

lemma pow_eq_one_iff_cases : a ^ n = 1 ↔ n = 0 ∨ a = 1 ∨ a = -1 ∧ Even n := by
  simp [← pow_eq_pow_iff_cases]

lemma pow_eq_neg_pow_iff (hb : b ≠ 0) : a ^ n = -b ^ n ↔ a = -b ∧ Odd n :=
  match n.even_or_odd with
  | .inl he =>
    suffices a ^ n > -b ^ n by simpa [he, not_odd_iff_even.2 he] using this.ne'
    lt_of_lt_of_le (by simp [he.pow_pos hb]) (he.pow_nonneg _)
  | .inr ho => by
    simp only [ho, and_true, ← ho.neg_pow, (ho.strictMono_pow (R := R)).injective.eq_iff]

lemma pow_eq_neg_one_iff : a ^ n = -1 ↔ a = -1 ∧ Odd n := by
  simpa using pow_eq_neg_pow_iff (R := R) one_ne_zero

end LinearOrderedField
