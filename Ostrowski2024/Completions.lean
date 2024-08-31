import Mathlib.Algebra.Order.CauSeq.Completion
import Mathlib

namespace CauSeq.Completion

open CauSeq

variable {α : Type*} [LinearOrderedField α]
variable {β : Type*} [Ring β] (abv : β → α) [IsAbsoluteValue abv]


local notation3 "abv_a" => fun x : α ↦ |x|

def Completion : Type u_1 := CauSeq.Completion.Cauchy abv_a

def abs_compl : CauSeq.Completion.Cauchy abv → CauSeq.Completion.Cauchy (fun x : α ↦ |x|) := by
  have f : CauSeq β abv → Cauchy abv_a := by
    intro s
    refine mk ?_
    let t := fun n ↦ abv (s.val n)
    have : IsCauSeq (fun x : α ↦ |x|) t := by
      intro e he
      sorry
    exact ⟨t, this⟩
  apply Quotient.lift f
  intro a b hab
  rw [← @mk_eq] at hab
  --apply CauSeq.ext


  sorry
