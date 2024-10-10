import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Int.WithZero
import Mathlib.Data.Rat.Star
import Mathlib.NumberTheory.Padics.PadicNorm
--import Ostrowski2024.WithZero
import Mathlib.NumberTheory.NumberField.Embeddings
import Mathlib.NumberTheory.Ostrowski
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.Ideal.Norm
import Mathlib.Tactic.Rify
import Mathlib.Topology.Algebra.Valued.NormedValued
import Mathlib.FieldTheory.Finite.Basic

--Product Formula

lemma fooN' {n : ℕ} (h_nezero : n ≠ 0) : { (p : Nat.Primes) | ((p : ℕ) ∣ n) }.Finite := by
  let f : Nat.Primes → ℕ := fun a => ↑a
  have : (f '' {p : Nat.Primes | ↑p ∣ n}).Finite := by
    apply Set.Finite.subset (Set.finite_le_nat n)
    simp only [Set.image_subset_iff, Set.preimage_setOf_eq]
    exact Set.setOf_subset_setOf.mpr (fun p hp => Nat.le_of_dvd (Nat.zero_lt_of_ne_zero h_nezero) hp)
  exact Set.Finite.of_finite_image this (Function.Injective.injOn Nat.Primes.coe_nat_injective)

lemma fooN {n : ℕ} (h_nezero : n ≠ 0) : (Function.mulSupport fun p : Nat.Primes => padicNorm p ↑n).Finite := by
  convert_to { (p : Nat.Primes) | ((p : ℕ) ∣ n) }.Finite
  · ext p
    have : Fact (Nat.Prime ↑p) := fact_iff.2 (p.2)
    have := padicNorm.of_nat (p:=↑p) n
    simp only [Function.mem_mulSupport, ne_eq, Set.mem_setOf_eq]
    rw [← padicNorm.nat_lt_one_iff]
    exact ⟨lt_of_le_of_ne this, ne_of_lt⟩
  · exact fooN' h_nezero

lemma Int.mulSupport_padicNorm_Finite {n : ℤ} (h_nezero : n ≠ 0) : (Function.mulSupport fun p : Nat.Primes => padicNorm ↑p ↑n).Finite := by
  have habs := Int.natAbs_eq n
  cases habs with
  | inl h =>
    rw [h]
    apply_mod_cast fooN (Int.natAbs_ne_zero.mpr h_nezero)
  | inr h =>
    rw [h]
    simp only [Int.cast_neg, Int.cast_abs, padicNorm.neg]
    apply_mod_cast fooN (Int.natAbs_ne_zero.mpr h_nezero)

theorem product_formula_N_range {x : ℕ} (h_x_nezero : x ≠ 0) : |(x : ℚ)| *
    ∏ p ∈ Finset.filter Nat.Prime (Finset.range (x + 1)), padicNorm p x = 1 := by
  nth_rw 1 [← Nat.prod_pow_prime_padicValNat x h_x_nezero (x + 1) (lt_add_one x)]
  have : (x : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr h_x_nezero
  simp_rw [padicNorm.eq_zpow_of_nonzero this]
  simp only [padicValRat.of_nat]
  rw [Nat.cast_prod, Finset.abs_prod, ← Finset.prod_mul_distrib]
  simp_all only [ne_eq, Nat.cast_eq_zero, not_false_eq_true, Nat.cast_pow, abs_pow, Nat.abs_cast,
    zpow_neg, zpow_natCast, pow_eq_zero_iff', padicValNat.eq_zero_iff, false_or, not_or,
    Decidable.not_not, not_and, zero_ne_one, zero_dvd_iff, and_false, implies_true, mul_inv_cancel₀,
    Finset.prod_const_one]


theorem product_formula_N {x : ℕ} (h_x_nezero : x ≠ 0) : |(x : ℚ)| * ∏ᶠ p : Nat.Primes, padicNorm p x = 1 := by
  rw [← product_formula_N_range h_x_nezero]
  simp only [Nat.abs_cast, mul_eq_mul_left_iff, Nat.cast_eq_zero]
  left
  have : {(p : Nat.Primes) | (p : ℕ) < x + 1}.Finite := by
    apply Set.Finite.of_finite_image _ (Function.Injective.injOn Nat.Primes.coe_nat_injective)
    let s := {m | m < x + 1}
    apply Finite.Set.subset s
    intro p hp
    simp only [Set.mem_setOf_eq, s]
    simp_all only [ne_eq, Set.mem_image, Set.mem_setOf_eq]
    obtain ⟨w, h⟩ := hp
    obtain ⟨left, right⟩ := h
    exact lt_of_eq_of_lt (id (Eq.symm right)) left
  have : Fintype  {(p : Nat.Primes) | (p : ℕ) < x + 1} := this.fintype
  let s : Finset Nat.Primes := by
    exact Set.toFinset {(p : Nat.Primes) | (p : ℕ) < x + 1}
  have h : (fooN h_x_nezero).toFinset ⊆ s := by
    intro p hp
    simp_all only [ne_eq, Nat.cast_eq_zero, not_false_eq_true, padicNorm.eq_zpow_of_nonzero,
      padicValRat.of_nat, zpow_neg, zpow_natCast, Function.mulSupport_inv, Set.Finite.mem_toFinset,
      Function.mem_mulSupport, s]
    refine Set.mem_toFinset.mpr ?_
    refine Set.mem_setOf.mpr ?_
    have : (p : ℕ) ∣ x := by
      rw [pow_eq_one_iff_cases] at hp
      simp only [padicValNat.eq_zero_iff, Nat.cast_eq_one, not_or, Decidable.not_not, not_and,
        Nat.not_even_iff_odd] at hp
      exact hp.1.2.2
    apply Nat.le_of_dvd (Nat.zero_lt_of_ne_zero h_x_nezero) at this
    exact Order.lt_add_one_iff.mpr this
  rw [finprod_eq_prod_of_mulSupport_toFinset_subset _ (fooN h_x_nezero) h]
  let e : Nat.Primes ↪ ℕ := {
    toFun := fun p => ↑p
    inj' := Nat.Primes.coe_nat_injective
  }
  let f : ℕ → ℚ := fun n => padicNorm n ↑x
  have h : Finset.filter Nat.Prime (Finset.range (x + 1)) = Finset.map e s := by
    simp only [e, s]
    simp_all only [ne_eq, Nat.cast_eq_zero, not_false_eq_true, padicNorm.eq_zpow_of_nonzero,
      padicValRat.of_nat, zpow_neg, zpow_natCast, Function.mulSupport_inv,
      Set.Finite.toFinset_subset, Function.mulSupport_subset_iff, Finset.mem_coe]
    refine Finset.ext_iff.mpr ?_
    intro p
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_map, Set.mem_toFinset,
      Set.mem_setOf_eq, Function.Embedding.coeFn_mk]
    constructor
    · intro h1
      use ⟨p, h1.2⟩
      exact And.symm (And.imp_left (fun _ => rfl) (id (And.symm h1)))
    · intro h1
      rcases h1 with ⟨p', hp1, hp2⟩
      constructor
      exact lt_of_eq_of_lt (id (Eq.symm hp2)) hp1
      rw [← hp2]
      exact p'.2
  rw [h, Finset.prod_map s e f]
  congr

theorem product_formula_Z {x : ℤ} (h_x_nezero : x ≠ 0) : |(x : ℚ)| * ∏ᶠ p : Nat.Primes, padicNorm p x = 1 := by
  have habs := Int.natAbs_eq x
  cases habs with
  | inl h =>
    rw [h]
    exact product_formula_N (Int.natAbs_ne_zero.mpr h_x_nezero)
  | inr h =>
    rw [h]
    simp only [Int.cast_neg, Int.cast_abs, abs_neg, abs_abs, padicNorm.neg]
    exact product_formula_N (Int.natAbs_ne_zero.mpr h_x_nezero)

theorem product_formula {x : ℚ} (h_x_nezero : x ≠ 0) : |x| * ∏ᶠ p : Nat.Primes, padicNorm p x = 1 := by
  rw [← Rat.num_div_den x, abs_div]
  have (p : Nat.Primes) : padicNorm p (↑x.num / ↑x.den) = padicNorm p (↑x.num) / padicNorm p (↑x.den) := by
    have : Fact (Nat.Prime ↑p) := by
      refine { out := ?out }
      exact p.2
    exact padicNorm.div ↑x.num ↑x.den
  rw [finprod_congr this, finprod_div_distrib (Int.mulSupport_padicNorm_Finite (Rat.num_ne_zero.mpr h_x_nezero))
    (mod_cast Int.mulSupport_padicNorm_Finite (mod_cast x.den_nz)), ← mul_div_assoc, mul_comm, mul_div_assoc,
    ← div_mul_eq_div_div, ← mul_div_assoc]
  nth_rw 1 [mul_comm]
  rw [product_formula_Z (Rat.num_ne_zero.mpr h_x_nezero), product_formula_N x.den_nz]
  exact one_div_one

namespace IsDedekindDomain.HeightOneSpectrum
variable {K : Type*} [Field K] [NumberField K]
open NumberField
variable (P : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) -- P is a nonzero prime ideal of 𝓞 K


lemma norm_ne_zero : (Nat.card <| 𝓞 K ⧸ P.asIdeal : NNReal) ≠ 0 := by
  set k := 𝓞 K ⧸ P.asIdeal
  have : Field k := Ideal.Quotient.field P.asIdeal
  have : Fintype k := Ideal.fintypeQuotientOfFreeOfNeBot P.asIdeal P.ne_bot
  simp_all only [Nat.card_eq_fintype_card, ne_eq, Nat.cast_eq_zero, Fintype.card_ne_zero, not_false_eq_true, k]

end IsDedekindDomain.HeightOneSpectrum

namespace NumberField
variable {K : Type*} [Field K] [NumberField K]
variable (P : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) -- P is a nonzero prime ideal of 𝓞 K
open IsDedekindDomain.HeightOneSpectrum  WithZeroMulInt

noncomputable def PadicNorm : K → ℝ := fun x =>
    toNNReal (norm_ne_zero P) ((IsDedekindDomain.HeightOneSpectrum.valuation P) x)

theorem PadicNorm_def (x : K) : PadicNorm P x =
    toNNReal (norm_ne_zero P) ((IsDedekindDomain.HeightOneSpectrum.valuation P) x) :=
    rfl

theorem Padic_norm_int_le_one (x : 𝓞 K) : PadicNorm P x ≤ 1 := by
  rw [PadicNorm_def]
  simp only [NNReal.coe_le_one]
  sorry

namespace PadicNorm

theorem div (a b : K) : PadicNorm P (a / b) = PadicNorm P a / PadicNorm P b := by
  rw [PadicNorm_def, PadicNorm_def, PadicNorm_def]
  simp only [map_div₀, NNReal.coe_div]

end PadicNorm

open PadicNorm

lemma mulSupport_PadicNorm_Finite_of_ideal_div_finite {x : 𝓞 K} (h_x_nezero : x ≠ 0)
    (h : {(P : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) | P.asIdeal ∣ Ideal.span {x}}.Finite) :
    (Function.mulSupport fun P : IsDedekindDomain.HeightOneSpectrum (𝓞 K) =>
    PadicNorm P x).Finite := by
  apply Set.Finite.subset h
  simp only [Ideal.dvd_span_singleton, Function.mulSupport_subset_iff, ne_eq, Set.mem_setOf_eq]
  intro P hp
  have : PadicNorm P ↑x < 1 := by sorry

  /- · ext P
    simp only [Function.mem_mulSupport, Set.mem_setOf_eq]
    rw [← @IsDedekindDomain.HeightOneSpectrum.valuation_lt_one_iff_dvd (𝓞 K) _ _ K _ _ _ P x,
      PadicNorm_def]
    simp only [ne_eq, NNReal.coe_eq_one]
    rw [@valuation_eq_intValuationDef]


    have : PadicNorm P ↑x ≠ 1 ↔ PadicNorm P ↑x < 1 := by

      sorry
    --rw [this]

    sorry -/
  sorry


theorem mulSupport_PadicNorm_Finite {x : 𝓞 K} (h_x_nezero : x ≠ 0) :
    (Function.mulSupport fun P : IsDedekindDomain.HeightOneSpectrum (𝓞 K) =>
    PadicNorm P x).Finite := by
  apply mulSupport_PadicNorm_Finite_of_ideal_div_finite h_x_nezero
  apply Ideal.finite_factors
  simp_all only [ne_eq, Submodule.zero_eq_bot, Ideal.span_singleton_eq_bot, not_false_eq_true]

theorem product_formula_int {x : 𝓞 K} (h_x_nezero : x ≠ 0) :
    ∏ᶠ P : IsDedekindDomain.HeightOneSpectrum (𝓞 K), PadicNorm P x = (|(Algebra.norm ℤ) x| : ℝ)⁻¹ := by sorry

theorem product_formula {x : K} (h_x_nezero : x ≠ 0) :
    ∏ᶠ P : IsDedekindDomain.HeightOneSpectrum (𝓞 K), PadicNorm P x = |(Algebra.norm ℚ) x|⁻¹ := by
  --reduce to 𝓞 K
  have : IsFractionRing (𝓞 K) K := NumberField.RingOfIntegers.instIsFractionRing
  have hfrac : ∃ a b : 𝓞 K, b ≠ 0 ∧  x = a / b := by
    rcases @IsFractionRing.div_surjective (𝓞 K) _ _ K _ _ _ x with ⟨a, b, hb, hfrac⟩
    use a, b
    subst hfrac
    simp_all only [ne_eq, div_eq_zero_iff, NoZeroSMulDivisors.algebraMap_eq_zero_iff, not_or, not_false_eq_true,
      and_self]
  rcases hfrac with ⟨a, b, hb, hx⟩
  simp_rw [hx]
  have (P : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) : PadicNorm P (a / b) = PadicNorm P a / PadicNorm P b := div P a b
  rw [finprod_congr this]
  simp only [Rat.cast_inv, Rat.cast_abs]
  have (y z : K) (h : z ≠ 0) : (Algebra.norm ℚ) (y / z) = ((Algebra.norm ℚ) y) / ((Algebra.norm ℚ) z) := by
    have : ((Algebra.norm ℚ) z) ≠ 0 := by
      subst hx
      simp_all only [ne_eq, div_eq_zero_iff, NoZeroSMulDivisors.algebraMap_eq_zero_iff, or_false,
        Algebra.norm_eq_zero_iff, not_false_eq_true]
    refine Eq.symm (IsUnit.div_eq_of_eq_mul (Ne.isUnit this) ?_)
    rw [← @MonoidHom.map_mul, div_mul, div_self h, div_one]
  rw [this _ _ (RingOfIntegers.coe_ne_zero_iff.mpr hb)]
  simp only [Rat.cast_div]
  rw [← Algebra.coe_norm_int a, ← Algebra.coe_norm_int b]
  simp only [Rat.cast_intCast]
  sorry



end NumberField
----#find_home! product_formula

--#find_home! product_formula_N_range

--#min_imports
