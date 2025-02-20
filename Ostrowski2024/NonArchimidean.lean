import Mathlib
--PR to Mathlib?
namespace AbsoluteValue

section Nonarchimedean

variable {R : Type*} {S : Type*}

def IsNonarchimedean [Semiring R] [LinearOrderedSemiring S] (f : AbsoluteValue R S) : Prop :=
  ∀ x y : R, f (x + y) ≤ max (f x) (f y)

open Finset in
/-- ultrametric inequality with Finset.Sum  -/
lemma nonarch_sum_sup [Semiring R] [LinearOrderedSemiring S] {f : AbsoluteValue R S}
    (nonarch : IsNonarchimedean f) {α : Type*} {s : Finset α} (hnonempty : s.Nonempty) {l : α → R} :
    f (∑ i ∈ s, l i) ≤ s.sup' hnonempty fun i => f (l i) := by
  apply Nonempty.cons_induction (p := fun a hn ↦ f (∑ i ∈ a, l i) ≤ a.sup' hn fun i ↦ f (l i))
  · simp
  · intro a s h hs hind
    simp only [le_sup'_iff, mem_cons, sum_cons, exists_eq_or_imp]
    rw [← le_sup'_iff hs]
    have h := le_max_iff.mp <| nonarch (l a) (∑ i ∈ s, l i)
    rcases h with h₁ | h₂
    · exact .inl h₁
    · exact .inr <| le_trans h₂ hind

lemma nonarch_nat_le_one [Semiring R] [Nontrivial R] [LinearOrderedRing S] [IsDomain S] {f : AbsoluteValue R S} (nonarch : IsNonarchimidean f) (n : ℕ) : f n ≤ 1 := by
  induction n with
  | zero => simp
  | succ n hn =>
    push_cast
    exact le_trans (nonarch n 1) (max_le hn <| le_of_eq f.map_one)

lemma nonarch_int_le_one [Nontrivial R] [Ring R] [LinearOrderedCommRing S] {f : AbsoluteValue R S} (nonarch : IsNonarchimedean f) (x : ℤ)  : f x ≤ 1 := by
  rw [← AbsoluteValue.apply_natAbs_eq]
  exact nonarch_nat_le_one nonarch x.natAbs

end Nonarchimedean

end AbsoluteValue

--#min_imports
