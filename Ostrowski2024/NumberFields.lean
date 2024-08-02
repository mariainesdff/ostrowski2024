import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.Analysis.Normed.Ring.Seminorm
import Ostrowski2024.Rationals
import Mathlib.Topology.Algebra.Valued.NormedValued
import Mathlib.RingTheory.Valuation.RankOne
import Mathlib.Algebra.Group.WithOne.Defs
--import Ostrowski2024.Hom
import Ostrowski2024.WithZero
import Mathlib.RingTheory.Ideal.Norm
import Mathlib.Algebra.Quotient
import Mathlib.FieldTheory.Finite.Basic

/-!
# Ostrowski's theorem for number fields

## References
* https://kconrad.math.uconn.edu/blurbs/gradnumthy/ostrowskiQ.pdf
* https://kconrad.math.uconn.edu/blurbs/gradnumthy/ostrowskinumbfield.pdf

## Tags
ring_norm, ostrowski
-/

/-!
Throughout this file, `f` is an arbitrary absolute value.
-/

open NumberField

variable (K : Type*) [Field K] [nf : NumberField K] (f : MulRingNorm K)

section restriction

variable (K' : Type*) [Field K'] [Algebra K' K]

def mulRingNorm_restriction : MulRingNorm K' :=
{ toFun     := fun x : K' ↦ f (x • (1 : K))
  map_zero' := by simp only [zero_smul, map_zero]
  add_le'   := by intro r s; simp only; rw [add_smul]; exact map_add_le_add f (r • 1) (s • 1)
  neg'      := by simp only [neg_smul, map_neg_eq_map, implies_true]
  eq_zero_of_map_eq_zero' := by simp only [map_eq_zero, smul_eq_zero, one_ne_zero, or_false,
    imp_self, implies_true]
  map_one' := by simp only [one_smul, map_one]
  map_mul' := by
    intro x y
    simp only
    nth_rw 1 [← one_mul (1 : K)]
    rw [← smul_mul_smul]
    exact MulHomClass.map_mul f (x • 1) (y • 1)
}

lemma restr_def (x : K') : (mulRingNorm_restriction K f K') x = f (x • (1 : K)) := rfl

lemma bdd_restr_Q : (∀ n : ℕ, f n ≤ 1) ↔  (∀ n : ℕ, (mulRingNorm_restriction K f ℚ) n ≤ 1) := by
  refine forall_congr' ?h
  intro n
  simp only [restr_def, Rat.smul_one_eq_cast, Rat.cast_natCast]

end restriction

section Archimedean

variable (notbdd : ¬ ∀ n : ℕ, f n ≤ 1)

noncomputable def mulRingNorm_arch (φ : K →+* ℂ) : MulRingNorm K :=
{ toFun     := fun x : K ↦ ‖φ x‖
  map_zero' := by simp only [map_zero, norm_zero]
  add_le'   := by intro r s; simp only [map_add, Complex.norm_eq_abs]
                  exact AbsoluteValue.add_le Complex.abs (φ r) (φ s)
  neg'      := by simp only [map_neg, norm_neg, Complex.norm_eq_abs, implies_true]
  eq_zero_of_map_eq_zero' := by simp only [Complex.norm_eq_abs, map_eq_zero, imp_self, implies_true]
  map_one' := by simp only [map_one, norm_one]
  map_mul' := by simp only [map_mul, norm_mul, Complex.norm_eq_abs, implies_true]
}

lemma restr_to_Q_real : MulRingNorm.equiv (mulRingNorm_restriction K f ℚ) Rational.mulRingNorm_real := by
  apply Rational.mulRingNorm_equiv_standard_of_unbounded
  intro h
  rw [← bdd_restr_Q] at h
  exact notbdd h

theorem ostr_arch :
    ∃ φ : K →+* ℂ, MulRingNorm.equiv f (mulRingNorm_arch K φ) := by
  rcases restr_to_Q_real K f notbdd with ⟨c, hc1, hc2⟩
  -- what follows is probably useless, need to work with completions.
  unfold MulRingNorm.equiv
  rw [exists_comm]
  use c
  rw [exists_and_left]
  refine ⟨hc1, ?_⟩
  sorry

end Archimedean

section Nonarchimedean



variable (P : IsDedekindDomain.HeightOneSpectrum (𝓞 K))

/- noncomputable def mulRingNorm_Padic : MulRingNorm K :=
{ toFun     := fun x : K ↦ (Zm0.toReal) (2⁻¹) (by simp only [inv_pos, Nat.ofNat_pos]) ((IsDedekindDomain.HeightOneSpectrum.valuation P) x)
  map_zero' := by simp only [map_zero]; exact rfl
  add_le'   := by
    simp only
    rw [Zm0.toReal_def]
    intro x y
    calc Zm0.toFun 2⁻¹ (P.valuation (x + y)) ≤  Zm0.toFun 2⁻¹ (P.valuation x) := by sorry
      _ ≤ Zm0.toFun 2⁻¹ (P.valuation x) + Zm0.toFun 2⁻¹ (P.valuation y) := by sorry
  neg'      := by simp only [Valuation.map_neg, implies_true]
  eq_zero_of_map_eq_zero' := by
    simp only
    intro x hx
    simp only [Zm0.toReal_def, MonoidHom.coe_mk, OneHom.coe_mk] at hx
    rw [Zm0.toFun_zero_iff _ _ (by simp only [inv_pos, Nat.ofNat_pos]), Valuation.zero_iff] at hx
    exact hx
  map_one' := by simp only [map_one]
  map_mul' := by simp only [map_mul, implies_true]
} -/

lemma foo : (2 : NNReal) ≠ 0 := by simp_all only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true]

lemma exist_prime_in_prime_ideal : ∃! (p : ℕ), ∃ (_ : Fact (p.Prime)), (↑p ∈ P.asIdeal) := by
  let r := Ideal.absNorm P.asIdeal
  set k := 𝓞 K ⧸ P.asIdeal
  have : Field k := Ideal.Quotient.field P.asIdeal
  have : Fintype k := Ideal.fintypeQuotientOfFreeOfNeBot P.asIdeal P.ne_bot
  rcases FiniteField.card' k with ⟨p, n, hp, hcard⟩
  have : r = p ^ (n : ℕ) := by
    rw [← hcard]
    simp only [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card, r, k]
  have hpmem : ↑p ∈ P.asIdeal := by
    apply Ideal.IsPrime.mem_of_pow_mem P.isPrime n
    norm_cast
    rw [← this]
    exact Ideal.absNorm_mem P.asIdeal
  use p
  constructor
  · simp only [exists_prop]
    refine ⟨{ out := hp }, hpmem⟩
  · intro q hq
    rcases hq with ⟨hq1, hq2⟩
    by_contra! hpq
    rw [← Nat.coprime_primes hq1.out hp] at hpq
    apply Nat.Coprime.isCoprime at hpq
    rcases hpq with ⟨a, b, hid⟩
    apply Ideal.mul_mem_left P.asIdeal a at hq2
    apply Ideal.mul_mem_left P.asIdeal b at hpmem
    have := Ideal.add_mem P.asIdeal hq2 hpmem
    norm_cast at this
    rw [hid] at this
    have hPprime := P.isPrime
    rw [Ideal.isPrime_iff] at hPprime
    apply hPprime.1
    rw [Ideal.eq_top_iff_one]
    exact_mod_cast this

noncomputable def prime_in_prime_ideal : ℕ := Exists.choose (exist_prime_in_prime_ideal K P)

lemma prime_in_prime_ideal_is_prime : Fact ((prime_in_prime_ideal K P).Prime) := (Exists.choose_spec (exist_prime_in_prime_ideal K P)).1.1

lemma p_ne_zero (p : ℕ) (hp : Fact (p.Prime)) : (p : NNReal) ≠ 0 := by
  simp only [ne_eq, Nat.cast_eq_zero]
  exact NeZero.ne p

lemma one_lt_p (p : ℕ) (hp : Fact (p.Prime)) : 1 < (p : NNReal) := mod_cast Nat.Prime.one_lt (Fact.elim hp)

--alternative (better adopt this one)
noncomputable def mulRingNorm_Padic' : MulRingNorm K :=
{ toFun     := fun x : K ↦ withZeroMultIntToNNReal (p_ne_zero (prime_in_prime_ideal K P) (prime_in_prime_ideal_is_prime K P)) (((IsDedekindDomain.HeightOneSpectrum.valuation P) x))
  map_zero' := by simp only [map_zero]; exact rfl
  add_le'   := by
    simp only
    let p := prime_in_prime_ideal K P
    let hp := prime_in_prime_ideal_is_prime K P
    intro x y
    norm_cast
    apply le_trans _ <| max_le_add_of_nonneg (by simp only [zero_le]) (by simp only [zero_le])
    have mono := StrictMono.monotone (withZeroMultIntToNNReal_strictMono (one_lt_p p hp))
    have h2 : (withZeroMultIntToNNReal (p_ne_zero p hp)) (max (P.valuation (x)) (P.valuation (y))) =
        max ((withZeroMultIntToNNReal (p_ne_zero p hp)) (P.valuation x)) ((withZeroMultIntToNNReal (p_ne_zero p hp))
        (P.valuation y)) := Monotone.map_max mono
    rw [← h2]
    exact mono (Valuation.map_add P.valuation x y)
  neg'      := by simp only [Valuation.map_neg, implies_true]
  eq_zero_of_map_eq_zero' := by simp_all only [NNReal.coe_eq_zero, map_eq_zero, implies_true]
  map_one' := by simp only [map_one, NNReal.coe_eq_one]
  map_mul' := by simp only [map_mul, NNReal.coe_mul, implies_true]
}


end Nonarchimedean
