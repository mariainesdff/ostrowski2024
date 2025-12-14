import Mathlib

open IsDedekindDomain HeightOneSpectrum WithZeroMulInt NumberField RingOfIntegers

variable {K : Type*} [Field K] [nf : NumberField K] (f : AbsoluteValue K ℝ)

section Nonarchimedean

open NumberField.RingOfIntegers.HeightOneSpectrum

--The next lemma is a general fact in algebraic number theory.
--This might be complicated, Conrad uses the class group but we might try with norms or minimal polynomials
-- Here https://feog.github.io/antchap6.pdf is a proof without class group
lemma exists_num_denom_absolute_value_one (α : K) (h_nezero : α ≠ 0) {v : HeightOneSpectrum (RingOfIntegers K)}
    (h_abs : adicAbv v α ≤ 1) : ∃ x y : 𝓞 K, α = x / y ∧ adicAbv v y = 1 := by
  sorry
