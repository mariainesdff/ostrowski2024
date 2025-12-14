/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 071d5200-9314-4559-a9f2-19839d9b93dc

The following was proved by Aristotle:

- lemma exists_num_denom_absolute_value_one (α : K) (h_nezero : α ≠ 0) {v : HeightOneSpectrum (RingOfIntegers K)}
    (h_abs : adicAbv v α ≤ 1) : ∃ x y : 𝓞 K, α = x / y ∧ adicAbv v y = 1
-/

import Mathlib


open IsDedekindDomain HeightOneSpectrum WithZeroMulInt NumberField RingOfIntegers

variable {K : Type*} [Field K] [nf : NumberField K] (f : AbsoluteValue K ℝ)

section Nonarchimedean

open NumberField.RingOfIntegers.HeightOneSpectrum

--The next lemma is a general fact in algebraic number theory.
--This might be complicated, Conrad uses the class group but we might try with norms or minimal polynomials
-- Here https://feog.github.io/antchap6.pdf is a proof without class group
noncomputable section AristotleLemmas

open IsDedekindDomain HeightOneSpectrum

theorem adicAbv_le_one_iff_valuation_le_one {R : Type*} [CommRing R] [IsDomain R] [IsDedekindDomain R] {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K] (v : HeightOneSpectrum R) {b : NNReal} (hb : 1 < b) (α : K) : v.adicAbv hb α ≤ 1 ↔ v.valuation K α ≤ 1 := by
  aesop;
  · exact (toNNReal_le_one_iff hb).mp a;
  · unfold IsDedekindDomain.HeightOneSpectrum.adicAbv; aesop;
    unfold IsDedekindDomain.HeightOneSpectrum.adicAbvDef;
    cases h : ( IsDedekindDomain.HeightOneSpectrum.valuation K v ) α <;> aesop;
    unfold WithZeroMulInt.toNNReal; aesop;

open IsDedekindDomain HeightOneSpectrum BigOperators

variable {R : Type*} [CommRing R] [IsDomain R] [IsDedekindDomain R]

theorem exists_mem_pow_not_mem_prime (v : HeightOneSpectrum R)
    (S : Finset (HeightOneSpectrum R)) (h_not_mem : v ∉ S) (e : HeightOneSpectrum R → ℕ) :
    ∃ y : R, y ∉ v.asIdeal ∧ ∀ w ∈ S, y ∈ w.asIdeal ^ (e w) := by
      -- Let $I = (v.asIdeal : Ideal R)$ and $J = \prod_{w \in S} (w.asIdeal : Ideal R)^{e w}$.
      set I := (v.asIdeal : Ideal R)
      set J := Finset.prod S (fun w => (w.asIdeal : Ideal R) ^ e w);
      -- Since $I$ and $J$ are coprime, there exist $a \in I$ and $b \in J$ such that $a + b = 1$.
      obtain ⟨a, b, haI, hbJ, hab⟩ : ∃ a ∈ I, ∃ b ∈ J, a + b = 1 := by
        have h_coprime : IsCoprime I J := by
          refine' IsCoprime.prod_right fun w hw => IsCoprime.pow_right _;
          simp +zetaDelta at *;
          -- Since $v$ and $w$ are distinct height one prime ideals, their corresponding maximal ideals are coprime.
          have h_coprime : v.asIdeal ≠ w.asIdeal := by
            exact fun h => h_not_mem ( by convert hw; aesop );
          exact?;
        norm_num +zetaDelta at *;
        exact?;
      refine' ⟨ haI, _, _ ⟩ <;> aesop;
      · exact v.2.ne_top ( by rw [ Ideal.eq_top_iff_one ] ; exact hab ▸ Ideal.add_mem _ b a_1 );
      · -- Since $haI \in J$, we have $haI \in w.asIdeal ^ e w$ for each $w \in S$ by definition of $J$.
        have h_mem_J : haI ∈ (∏ w ∈ S, (w.asIdeal : Ideal R) ^ e w) := by
          exact hbJ;
        exact Ideal.le_of_dvd ( Finset.dvd_prod_of_mem _ a_1 ) h_mem_J

open IsDedekindDomain HeightOneSpectrum BigOperators

variable {R : Type*} [CommRing R] [IsDomain R] [IsDedekindDomain R]
variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

theorem finite_valuation_gt_one (α : K) : { v : HeightOneSpectrum R | 1 < v.valuation K α }.Finite := by
  by_cases h : α = 0;
  · aesop;
  · -- Write $\alpha = a/b$ with $a, b \in R, b \ne 0$.
    obtain ⟨a, b, ha, hb, hab⟩ : ∃ a b : R, b ≠ 0 ∧ (algebraMap R K a) / (algebraMap R K b) = α := by
      obtain ⟨ a, b, hb, h ⟩ := IsLocalization.mk'_surjective ( nonZeroDivisors R ) α;
      use a.1, a.2; aesop;
    -- Since $v(\alpha) = v(a)/v(b)$, we have $v(\alpha) > 1$ if and only if $v(b) < 1$.
    suffices h_finite : {v : HeightOneSpectrum R | v.valuation K (algebraMap R K b) < 1}.Finite by
      refine' h_finite.subset _;
      intro v hv
      aesop;
      contrapose! hv;
      exact div_le_one_of_le₀ ( le_trans ( IsDedekindDomain.HeightOneSpectrum.valuation_le_one v a ) hv ) ( by aesop );
    refine' Set.Finite.subset ( Ideal.finite_factors _ ) _;
    exact Ideal.span { b };
    · aesop;
    · aesop;
      exact?

open IsDedekindDomain HeightOneSpectrum BigOperators

variable {R : Type*} [CommRing R] [IsDomain R] [IsDedekindDomain R]
variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

theorem exists_pow_mul_le (w : HeightOneSpectrum R) (α : K) :
    ∃ n : ℕ, ∀ y : R, y ∈ w.asIdeal ^ n → w.valuation K (algebraMap R K y) * w.valuation K α ≤ 1 := by
      by_contra! h;
      choose f hf using h;
      -- Since $f x \in w.asIdeal ^ x$, we have $w.valuation K (algebraMap R K (f x)) \leq Multiplicative.ofAdd (-x)$.
      have h_val : ∀ x : ℕ, w.valuation K (algebraMap R K (f x)) ≤ Multiplicative.ofAdd (-x : ℤ) := by
        intro x;
        have := hf x;
        rw [ IsDedekindDomain.HeightOneSpectrum.valuation ] at * ; aesop;
        have := w.intValuation_le_pow_iff_mem ( f x ) x; aesop;
      -- Since $w.valuation K α$ is a value in $ℤₘ₀$, and $ℤₘ₀$ is bounded by $Multiplicative.ofAdd n$ for large enough $n$ (unless it's $∞$ which is not possible for $K$), such $n$ exists.
      obtain ⟨n, hn⟩ : ∃ n : ℕ, w.valuation K α ≤ Multiplicative.ofAdd (n : ℤ) := by
        by_cases hα : α = 0;
        · aesop;
        · obtain ⟨n, hn⟩ : ∃ n : ℤ, w.valuation K α = Multiplicative.ofAdd n := by
            cases h : w.valuation K α ; aesop;
            exact ⟨ _, rfl ⟩;
          cases' Int.eq_nat_or_neg n with hn hn ; aesop;
      refine' hf ( n + 1 ) |>.2.not_le _;
      refine' le_trans ( mul_le_mul' ( h_val _ ) hn ) _ ; simp +decide [ ← WithZero.coe_mul ]

open NumberField BigOperators

variable {K : Type*} [Field K] [NumberField K]

theorem variable_fixer : True := trivial

open IsDedekindDomain HeightOneSpectrum

def check_dedekind_adicAbv_lemma (R : Type*) [CommRing R] [IsDomain R] [IsDedekindDomain R] (v : HeightOneSpectrum R) {b : NNReal} (hb : 1 < b) (r : R) : v.adicAbv hb (algebraMap R (FractionRing R) r) = 1 ↔ r ∉ v.asIdeal := IsDedekindDomain.HeightOneSpectrum.adicAbv_coe_eq_one_iff v hb r

open NumberField.RingOfIntegers.HeightOneSpectrum

def check_nf_adicAbv_exists (K : Type*) [Field K] [NumberField K] (v : HeightOneSpectrum (RingOfIntegers K)) : AbsoluteValue K ℝ := adicAbv v

#check adicAbv

open NumberField.RingOfIntegers.HeightOneSpectrum IsDedekindDomain

theorem adicAbv_eq_dedekind_adicAbv {K : Type*} [Field K] [NumberField K] (v : HeightOneSpectrum (RingOfIntegers K)) :
    adicAbv v = IsDedekindDomain.HeightOneSpectrum.adicAbv v (one_lt_absNorm_nnreal v) := rfl

end AristotleLemmas

lemma exists_num_denom_absolute_value_one (α : K) (h_nezero : α ≠ 0) {v : HeightOneSpectrum (RingOfIntegers K)}
    (h_abs : adicAbv v α ≤ 1) : ∃ x y : 𝓞 K, α = x / y ∧ adicAbv v y = 1 := by
  -- Let $S = {w : IsDedekindDomain.HeightOneSpectrum (RingOfIntegers K) | 1 < w.valuation K α}$ and $S$ is finite by `finite_valuation_gt_one`.
  set S := {w : IsDedekindDomain.HeightOneSpectrum (RingOfIntegers K) | 1 < w.valuation K α} with hS_def
  have hS_finite : S.Finite := by
    exact?;
  -- For each $w \in S$, use `exists_pow_mul_le w α` to find an exponent $n_w$ such that $\forall y \in w.asIdeal ^ n_w, w.valuation K y * w.valuation K α \leq 1$.
  obtain ⟨n, hn⟩ : ∃ n : IsDedekindDomain.HeightOneSpectrum (RingOfIntegers K) → ℕ, ∀ w ∈ hS_finite.toFinset, ∀ y : RingOfIntegers K, y ∈ w.asIdeal ^ n w → w.valuation K y * w.valuation K α ≤ 1 := by
    have hn : ∀ w ∈ hS_finite.toFinset, ∃ n : ℕ, ∀ y : RingOfIntegers K, y ∈ w.asIdeal ^ n → w.valuation K y * w.valuation K α ≤ 1 := by
      intro w hw;
      exact?;
    choose! n hn using hn;
    use n;
  -- Use `exists_mem_pow_not_mem_prime v hS_finite.toFinset ... n` to find `y ∈ 𝓞 K` such that `y ∉ v.asIdeal` and `∀ w ∈ S, y ∈ w.asIdeal ^ (n w)`.
  obtain ⟨y, hy₁, hy₂⟩ : ∃ y : RingOfIntegers K, y ∉ v.asIdeal ∧ ∀ w ∈ hS_finite.toFinset, y ∈ w.asIdeal ^ n w := by
    have := exists_mem_pow_not_mem_prime v hS_finite.toFinset;
    apply this;
    norm_num +zetaDelta at *;
    convert adicAbv_le_one_iff_valuation_le_one v ( one_lt_absNorm_nnreal v ) α |>.1 h_abs using 1;
  -- Let $x = y * α$. We claim $x ∈ 𝓞 K$.
  have hx_mem : ∃ x : RingOfIntegers K, (algebraMap (RingOfIntegers K) K x) = y * α := by
    have hx_mem : ∀ w : IsDedekindDomain.HeightOneSpectrum (RingOfIntegers K), w.valuation K (algebraMap (RingOfIntegers K) K y * α) ≤ 1 := by
      intro w
      by_cases hwS : w ∈ S;
      · aesop;
      · simp +zetaDelta at *;
        refine' le_trans ( mul_le_mul_left' hwS _ ) _;
        simp +zetaDelta at *;
        exact?;
    apply IsDedekindDomain.HeightOneSpectrum.mem_integers_of_valuation_le_one; assumption;
  obtain ⟨ x, hx ⟩ := hx_mem;
  refine' ⟨ x, y, _, _ ⟩;
  · rw [ eq_div_iff ] <;> norm_cast at * ; aesop;
    · ring;
    · exact fun h => hy₁ <| h.symm ▸ v.asIdeal.zero_mem;
  · convert adicAbv_coe_eq_one_iff v ( one_lt_absNorm_nnreal v ) y |>.2 hy₁
