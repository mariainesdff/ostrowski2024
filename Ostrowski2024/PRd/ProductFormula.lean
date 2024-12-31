import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Int.WithZero
import Mathlib.Data.Rat.Star
import Mathlib.NumberTheory.Padics.PadicNorm
import Ostrowski2024.WithZero
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

/- ## Number Field case  -/

namespace IsDedekindDomain.HeightOneSpectrum
variable {R : Type u_1} [CommRing R] [IsDedekindDomain R] (P : IsDedekindDomain.HeightOneSpectrum R)

/-- The set of maximal ideals that contain `x`. -/
def support_set (x : R) : Set (HeightOneSpectrum R) :=
    {v : HeightOneSpectrum R | x ∈ v.asIdeal}

/-- If `x ≠ 0` the set of maximal ideals that contain `x` is finite. -/
lemma support_set_finite_of_nezero {x : R} (hx : x ≠ 0) : (support_set x).Finite := by
  have h : {(P : HeightOneSpectrum R) | P.asIdeal ∣ Ideal.span {x}}.Finite := by
    apply Ideal.finite_factors
    simp_all only [ne_eq, Submodule.zero_eq_bot, Ideal.span_singleton_eq_bot, not_false_eq_true]
  apply Set.Finite.subset h
  simp_all only [ne_eq, Ideal.dvd_span_singleton]
  rfl

/-- The Finset of maximal ideals that contain `x ≠ 0`. -/
noncomputable def support {x : R} (hx : x ≠ 0) : Finset (IsDedekindDomain.HeightOneSpectrum R) :=
    Set.Finite.toFinset (support_set_finite_of_nezero hx)

lemma support_def {x : R} (hx : x ≠ 0) : support hx = Set.Finite.toFinset (support_set_finite_of_nezero hx) := rfl

lemma mem_support_iff_mem_ideal {x : R} (hx : x ≠ 0) : P ∈ support hx ↔ x ∈ P.asIdeal := by
  rw [support_def, Set.Finite.mem_toFinset]
  rfl

end IsDedekindDomain.HeightOneSpectrum

namespace NumberField
variable {K : Type*} [Field K] [NumberField K]
variable (P : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) -- P is a nonzero prime ideal of 𝓞 K

/-- The norm of a maximal ideal as an element of ℝ≥0 is > 1  -/
lemma one_lt_norm : 1 < (Nat.card <| 𝓞 K ⧸ P.asIdeal : NNReal) := by
  set k := 𝓞 K ⧸ P.asIdeal
  have : Field k := Ideal.Quotient.field P.asIdeal
  have : Fintype k := Ideal.fintypeQuotientOfFreeOfNeBot P.asIdeal P.ne_bot
  rcases FiniteField.card' k with ⟨p, n, hp, hcard⟩
  simp only [Nat.card_eq_fintype_card, hcard]
  norm_cast
  refine Nat.one_lt_pow (PNat.ne_zero n) (Nat.Prime.one_lt hp)

/-- The norm of a maximal ideal as an element of ℝ≥0 is non zero   -/
lemma norm_ne_zero : (Nat.card <| 𝓞 K ⧸ P.asIdeal : NNReal) ≠ 0 := ne_zero_of_lt (one_lt_norm P)

open IsDedekindDomain.HeightOneSpectrum  WithZeroMulInt

/-- The Padic norm with respect to a maximal ideal.  -/
noncomputable def PadicNorm : K → ℝ := fun x =>
    toNNReal (norm_ne_zero P) ((IsDedekindDomain.HeightOneSpectrum.valuation P) x)

theorem PadicNorm_def (x : K) : PadicNorm P x =
    toNNReal (norm_ne_zero P) ((IsDedekindDomain.HeightOneSpectrum.valuation P) x) :=
    rfl

lemma Padic_norm_zero : PadicNorm P 0 = 0 := by
  rw [PadicNorm_def]
  exact_mod_cast toNNReal_pos_apply _ (Valuation.map_zero P.valuation)

theorem Padic_norm_int_le_one (x : 𝓞 K) : PadicNorm P x ≤ 1 := by
  by_cases h : x = 0
  · rw [h]
    simp only [map_zero, Padic_norm_zero]
    exact zero_le_one' ℝ
  · rw [PadicNorm_def]
    simp only [NNReal.coe_le_one]
    rw [le_one (one_lt_norm P)]
    exact valuation_le_one P x

namespace PadicNorm

theorem div (a b : K) : PadicNorm P (a / b) = PadicNorm P a / PadicNorm P b := by
  rw [PadicNorm_def, PadicNorm_def, PadicNorm_def]
  simp only [map_div₀, NNReal.coe_div]

end PadicNorm

open PadicNorm

lemma mul_support_subset_support {x : 𝓞 K} (h_x_nezero : x ≠ 0) :
    (Function.mulSupport fun P : IsDedekindDomain.HeightOneSpectrum (𝓞 K) => PadicNorm P x) ⊆
    support h_x_nezero := by
  intro P hP
  rw [@Function.mem_mulSupport] at hP
  have : PadicNorm P ↑x < 1 := by
    have := Padic_norm_int_le_one P x
    exact lt_of_le_of_ne this hP
  rw [PadicNorm_def] at this
  norm_cast at this
  rw [lt_one (one_lt_norm P),
    IsDedekindDomain.HeightOneSpectrum.valuation_eq_intValuationDef,
    IsDedekindDomain.HeightOneSpectrum.intValuation_lt_one_iff_dvd] at this
  norm_cast
  rw [mem_support_iff_mem_ideal]
  simp_all only [ne_eq, Ideal.dvd_span_singleton]

theorem mulSupport_PadicNorm_Finite {x : 𝓞 K} (h_x_nezero : x ≠ 0) :
    (Function.mulSupport fun P : IsDedekindDomain.HeightOneSpectrum (𝓞 K) =>
    PadicNorm P x).Finite := Set.Finite.subset (Finset.finite_toSet (support h_x_nezero)) (mul_support_subset_support h_x_nezero)

lemma Pow_Dividing_mulSupport_subset_Padic_mulSupport {x : 𝓞 K} (h_x_nezero : x ≠ 0) :
    (Function.mulSupport fun P : IsDedekindDomain.HeightOneSpectrum (𝓞 K) => P.maxPowDividing (Ideal.span {x})) ⊆ (Function.mulSupport fun P : IsDedekindDomain.HeightOneSpectrum (𝓞 K) =>
    PadicNorm P x) := by
  intro P hP
  simp_all only [Function.mem_mulSupport]
  rw [PadicNorm_def]
  norm_cast
  rw [eq_one _ (Ne.symm (ne_of_lt (one_lt_norm P))) (by simp_all only [ne_eq, map_eq_zero,
    NoZeroSMulDivisors.algebraMap_eq_zero_iff, not_false_eq_true]),
    IsDedekindDomain.HeightOneSpectrum.valuation_eq_intValuationDef,
    IsDedekindDomain.HeightOneSpectrum.intValuationDef_if_neg P h_x_nezero]
  norm_cast
  simp only [ofAdd_neg, inv_eq_one, ofAdd_eq_one, Nat.cast_eq_zero]
  intro h
  apply hP
  rw [IsDedekindDomain.HeightOneSpectrum.maxPowDividing, h, pow_zero _]

lemma Pow_Dividing_mulSupport_subset_support {x : 𝓞 K} (h_x_nezero : x ≠ 0) :
    (Function.mulSupport fun P : IsDedekindDomain.HeightOneSpectrum (𝓞 K) => P.maxPowDividing (Ideal.span {x})) ⊆
    support h_x_nezero := subset_trans (Pow_Dividing_mulSupport_subset_Padic_mulSupport h_x_nezero) (mul_support_subset_support h_x_nezero)

theorem product_formula_int {x : 𝓞 K} (h_x_nezero : x ≠ 0) :
    ∏ᶠ P : IsDedekindDomain.HeightOneSpectrum (𝓞 K), PadicNorm P x = (|(Algebra.norm ℤ) x| : ℝ)⁻¹ := by
  apply Eq.symm (inv_eq_of_mul_eq_one_left _)
  norm_cast
  have h_span_nezero : Ideal.span {x} ≠ 0 := by
    simp_all only [ne_eq, Submodule.zero_eq_bot, Ideal.span_singleton_eq_bot, not_false_eq_true]
  rw [Int.abs_eq_natAbs, ← Ideal.absNorm_span_singleton,
    ← Ideal.finprod_heightOneSpectrum_factorization h_span_nezero]
  simp only [Int.cast_natCast]
  have := mul_support_subset_support h_x_nezero
  rw [finprod_eq_prod_of_mulSupport_toFinset_subset (s:=support h_x_nezero) _ (mulSupport_PadicNorm_Finite h_x_nezero) (Set.Finite.toFinset_subset.mpr this),
    finprod_eq_prod_of_mulSupport_toFinset_subset (s:=support h_x_nezero) _
    (Ideal.finite_mulSupport h_span_nezero) (Set.Finite.toFinset_subset.mpr
    (Pow_Dividing_mulSupport_subset_support h_x_nezero)), map_prod]
  push_cast
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_eq_one
  intro P _
  rw [IsDedekindDomain.HeightOneSpectrum.maxPowDividing]
  simp only [map_pow, Nat.cast_pow]
  rw [PadicNorm_def, WithZeroMulInt.toNNReal_neg_apply _ (by simp only [ne_eq, map_eq_zero, NoZeroSMulDivisors.algebraMap_eq_zero_iff]; exact h_x_nezero),
    Ideal.absNorm_apply, Submodule.cardQuot_apply]
  push_cast
  rw [← Real.rpow_natCast, ← Real.rpow_intCast, ← Real.rpow_add (mod_cast Nat.zero_lt_of_lt (mod_cast one_lt_norm P))]
  norm_cast
  rw [zpow_eq_one_iff_right₀ (Nat.cast_nonneg' (Nat.card (𝓞 K ⧸ P.asIdeal))) (by exact Ne.symm (ne_of_lt (one_lt_norm P)))]
  simp_rw [valuation_eq_intValuationDef P x, intValuationDef_if_neg P h_x_nezero]
  simp only [ofAdd_neg, WithZero.coe_inv, WithZero.unzero_coe, toAdd_inv, toAdd_ofAdd,
    neg_add_cancel]

theorem product_formula_finite {x : K} (h_x_nezero : x ≠ 0) :
    ∏ᶠ P : IsDedekindDomain.HeightOneSpectrum (𝓞 K), PadicNorm P x = |(Algebra.norm ℚ) x|⁻¹ := by
  --reduce to 𝓞 K
  have : IsFractionRing (𝓞 K) K := NumberField.RingOfIntegers.instIsFractionRing
  have hfrac : ∃ a b : 𝓞 K, b ≠ 0 ∧  x = a / b := by
    rcases @IsFractionRing.div_surjective (𝓞 K) _ _ K _ _ _ x with ⟨a, b, _, hfrac⟩
    use a, b
    subst hfrac
    simp_all only [ne_eq, div_eq_zero_iff, NoZeroSMulDivisors.algebraMap_eq_zero_iff, not_or, not_false_eq_true,
      and_self]
  rcases hfrac with ⟨a, b, hb, hx⟩
  have ha : a ≠ 0 := by
    subst hx
    simp_all only [ne_eq, div_eq_zero_iff, NoZeroSMulDivisors.algebraMap_eq_zero_iff, or_false, not_false_eq_true]
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
  rw [finprod_div_distrib (mulSupport_PadicNorm_Finite ha) (mulSupport_PadicNorm_Finite hb),
    product_formula_int ha, product_formula_int hb, abs_div]
  simp only [div_inv_eq_mul, inv_div, inv_mul_eq_div]

theorem product_formula {x : K} (h_x_nezero : x ≠ 0) :
    (∏ w : NumberField.InfinitePlace K, w x ^ w.mult) * ∏ᶠ P : IsDedekindDomain.HeightOneSpectrum (𝓞 K), PadicNorm P x = 1 := by
  rw [product_formula_finite h_x_nezero, NumberField.InfinitePlace.prod_eq_abs_norm x]
  simp_all only [ne_eq, Rat.cast_abs, Rat.cast_inv, isUnit_iff_ne_zero, abs_eq_zero, Rat.cast_eq_zero,
    Algebra.norm_eq_zero_iff, not_false_eq_true, IsUnit.mul_inv_cancel]

end NumberField
--#find_home! NumberField.product_formula

--#find_home! product_formula_N_range

--#min_imports
