import Mathlib.Algebra.Group.WithOne.Defs
import Mathlib.Algebra.Quotient
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.NumberTheory.NumberField.Embeddings
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.Ideal.Norm
import Mathlib.Topology.Algebra.Valued.NormedValued
import Ostrowski2024.Rationals
import Ostrowski2024.WithZero


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

variable {K : Type*} [Field K] (f g : MulRingNorm K)

section completion

instance MulRingNorm_is_absolute_value : IsAbsoluteValue f := {
  abv_nonneg' := apply_nonneg f
  abv_eq_zero' := map_eq_zero f
  abv_add' := map_add_le_add f
  abv_mul' := MulHomClass.map_mul f
}

def Completion : Type u_1 := CauSeq.Completion.Cauchy f

/- lemma Completion_equiv : MulRingNorm.equiv f g ↔ Completion f = Completion g := by
  constructor
  · intro h
    rcases h with ⟨c, hc1, hc2⟩
    unfold Completion
    unfold CauSeq.Completion.Cauchy
    unfold Quotient

    --apply Quot.sound

    sorry
  · sorry -/

end completion

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

lemma restr_def (x : K') : (mulRingNorm_restriction f K') x = f (x • (1 : K)) := rfl

end restriction


open NumberField

variable {K : Type*} [Field K] [nf : NumberField K] [DecidableEq K] (f : MulRingNorm K)
  (hf_nontriv : f ≠ 1)

theorem non_arch_iff_bdd : (∀ n : ℕ, f n ≤ 1) ↔  ∀ x y : K, f (x + y) ≤ max (f x) (f y) := by
--https://zb260.user.srcf.net/notes/III/local.pdf Lemma 3.5
  constructor
  · sorry
  · sorry

lemma bdd_restr_Q : (∀ n : ℕ, f n ≤ 1) ↔ (∀ n : ℕ, (mulRingNorm_restriction f ℚ) n ≤ 1) := by
  refine forall_congr' ?h
  intro n
  simp only [restr_def, Rat.smul_one_eq_cast, Rat.cast_natCast]

section Archimedean

variable (notbdd : ¬ ∀ n : ℕ, f n ≤ 1)

-- Archimedean mulRingNorm associated to a complex embedding
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

/--The restriction of an archimedean MulRingNorm to the rational is the standard absolute value -/
lemma restr_to_Q_real : MulRingNorm.equiv (mulRingNorm_restriction f ℚ) Rational.mulRingNorm_real := by
  apply Rational.mulRingNorm_equiv_standard_of_unbounded
  intro h
  rw [← bdd_restr_Q] at h
  exact notbdd h

/-- Archimedean Ostrowski -/
theorem ostr_arch :
    ∃ φ : K →+* ℂ, (MulRingNorm.equiv f (mulRingNorm_arch φ) ∧
    ∀ ψ : K →+* ℂ, (MulRingNorm.equiv f (mulRingNorm_arch ψ)) →
    (ψ = φ ∨ NumberField.ComplexEmbedding.conjugate ψ = φ) ) := by
  -- pull ∃ c outside
  convert_to ∃ c : ℝ, 0 < c ∧ (∃ φ, (fun x => f x ^ c) = ⇑(mulRingNorm_arch φ) ∧ (∀ (ψ : K →+* ℂ), f.equiv (mulRingNorm_arch ψ) → ψ = φ ∨ ComplexEmbedding.conjugate ψ = φ))
  constructor
  · intro h
    rcases h with ⟨φ, h1, h2⟩
    rcases h1 with ⟨c, hc⟩
    use c
    refine ⟨hc.1, ?_⟩
    use φ
    exact And.symm (And.imp_left (fun a => h2) hc)
  · intro h
    rcases h with ⟨c , h1, h2⟩
    rcases h2 with ⟨φ, h3⟩
    use φ
    refine ⟨?_, h3.2⟩
    use c
    exact And.imp_left (fun a => h1) (id (And.symm h3))
  rcases restr_to_Q_real f notbdd with ⟨c, hc1, hc2⟩
  use c
  refine ⟨hc1, ?_⟩
  set K₀ := Completion f with hcomplK
  have hfK₀ : Field K₀ := CauSeq.Completion.Cauchy.field
  set Q₀ := Completion (mulRingNorm_restriction f ℚ) with hcomplQ
  have hfQ₀ : Field Q₀ := CauSeq.Completion.Cauchy.field
  --have F : ℝ ≃+* Q₀ := Real.ringEquivCauchy

  have : Q₀ ≃+* ℝ := by
    refine {
      toEquiv := by
        refine Equiv.ofBijective ?f ?hf
        simp [Q₀]
        unfold Completion
        intro s
        sorry
        sorry
      map_mul' := by sorry
      map_add' := by sorry
    }
    --simp [Q₀]
    --unfold Completion



  rcases Field.exists_primitive_element ℚ K with ⟨γ, hγ⟩

  --  CauSeq.Completion.ofRat : The map from the original ring into the Cauchy completion.


  sorry

end Archimedean

section Nonarchimedean

section mulRingNorm_Padic_def

variable (P : IsDedekindDomain.HeightOneSpectrum (𝓞 K))

/-- A non zero prime ideal of 𝓞 K contains a unique prime number -/
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
    have := Ideal.add_mem P.asIdeal (Ideal.mul_mem_left P.asIdeal a hq2) (Ideal.mul_mem_left P.asIdeal b hpmem)
    rw_mod_cast [hid] at this
    have hPprime := P.isPrime
    rw [Ideal.isPrime_iff] at hPprime
    apply hPprime.1
    rw [Ideal.eq_top_iff_one]
    exact_mod_cast this

/-- The unique prime number contained in P -/
noncomputable def prime_in_prime_ideal : ℕ := Exists.choose (exist_prime_in_prime_ideal P)

lemma prime_in_prime_ideal_is_prime : Fact ((prime_in_prime_ideal P).Prime) := (Exists.choose_spec (exist_prime_in_prime_ideal P)).1.1

lemma p_ne_zero (p : ℕ) (hp : Fact (p.Prime)) : (p : NNReal) ≠ 0 := by
  simp only [ne_eq, Nat.cast_eq_zero]
  exact NeZero.ne p

lemma one_lt_p (p : ℕ) (hp : Fact (p.Prime)) : 1 < (p : NNReal) := mod_cast Nat.Prime.one_lt (Fact.elim hp)

/--The P-adic absolute value -/
-- Now we have p ^ - v_p (x). Do we want to add the ramification index of P as a factor in the exponent?
noncomputable def mulRingNorm_Padic : MulRingNorm K :=
{ toFun     := fun x : K ↦ withZeroMultIntToNNReal (p_ne_zero (prime_in_prime_ideal P) (prime_in_prime_ideal_is_prime P)) (((IsDedekindDomain.HeightOneSpectrum.valuation P) x))
  map_zero' := by simp only [map_zero]; exact rfl
  add_le'   := by
    simp only
    let p := prime_in_prime_ideal P
    let hp := prime_in_prime_ideal_is_prime P
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

end mulRingNorm_Padic_def

variable (nonarch : ∀ x y : K, f (x + y) ≤ max (f x) (f y))

/-- 𝓞 K is contained in the closed unit ball -/
lemma integers_closed_unit_ball (x : 𝓞 K) : f x ≤ 1 := by
  sorry

-- open unit ball in 𝓞 K
local notation3 "𝓟" => {a : (𝓞 K) | f a < 1}

/-- The open unit ball in 𝓞 K is a non-zero prime ideal of 𝓞 K. -/
lemma exists_ideal : ∃ P : IsDedekindDomain.HeightOneSpectrum (𝓞 K), 𝓟 = P.asIdeal.carrier := by
  use
  { asIdeal := {carrier   := 𝓟
                add_mem'  := by
                  simp only [Set.mem_setOf_eq, map_add]
                  exact fun ha hb => lt_of_le_of_lt (nonarch _ _) (max_lt ha hb)
                zero_mem' := by simp only [Set.mem_setOf_eq, map_zero, zero_lt_one]
                smul_mem' := by
                  simp only [Set.mem_setOf_eq, smul_eq_mul, map_mul]
                  exact fun c x hx => Right.mul_lt_one_of_le_of_lt_of_nonneg
                    (integers_closed_unit_ball f c) hx (apply_nonneg f ↑x)
                }
    isPrime := by
      rw [Ideal.isPrime_iff]
      constructor
      -- P is not 𝓞 K:
      · rw [Ideal.ne_top_iff_one]
        simp only [Submodule.mem_mk, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk,
          Set.mem_setOf_eq, map_one, lt_self_iff_false, not_false_eq_true]
      -- x * y ∈ P → x ∈ P ∨ y ∈ P:
      · simp only [Submodule.mem_mk, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk,
        Set.mem_setOf_eq, map_mul]
        intro x y hxy
        --easy
        sorry
    ne_bot  := by
      -- P ≠ 0
      sorry
  }

theorem Ostr_nonarch : ∃! P : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
    MulRingNorm.equiv f (mulRingNorm_Padic P) := by
  rcases exists_ideal f nonarch with ⟨P, hP⟩
  rcases IsDedekindDomain.HeightOneSpectrum.intValuation_exists_uniformizer P with ⟨π, hπ⟩ --uniformizer, this will give the constant of the equivalence
  use P
  constructor
  · --existence
    sorry
  · --uniqueness
    intro Q hQ
    sorry

end Nonarchimedean
