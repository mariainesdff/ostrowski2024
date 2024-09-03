import Mathlib.Algebra.Order.CauSeq.Completion
import Mathlib

namespace CauSeq.Completion

open CauSeq

variable {α : Type*} [LinearOrderedField α]
variable {β : Type*} [Ring β] (abv : β → α) [IsAbsoluteValue abv]

def abs_compl : CauSeq.Completion.Cauchy abv → CauSeq.Completion.Cauchy (fun x : α ↦ |x|) := by
  have h_abs_Cau (s : CauSeq β abv) : IsCauSeq (fun x : α ↦ |x|) (abv ∘ s.val) := by
    intro e he
    rcases s.2 e he with ⟨i, h⟩
    use i
    intro j hj
    specialize h j hj
    refine abs_sub_lt_iff.mpr ?h.a
    refine ⟨lt_of_le_of_lt (IsAbsoluteValue.sub_abv_le_abv_sub abv (↑(s j)) (↑(s i))) h, ?_ ⟩
    apply lt_of_le_of_lt (IsAbsoluteValue.sub_abv_le_abv_sub abv (↑(s i)) (↑(s j))) _
    rwa [IsAbsoluteValue.abv_sub abv (↑(s i)) (↑(s j))]
  let abv' : CauSeq β abv → CauSeq α (fun x : α ↦ |x|) := fun s => ⟨abv ∘ s.val , h_abs_Cau s⟩
  apply Quotient.lift (fun s ↦ mk (abv' s))
  intro a b hab
  rw [← Quotient.out_equiv_out]
  have h (c : CauSeq β abv) : (Quotient.out (mk (abv' c))) ≈ (abv' c) := by exact Quotient.eq_mk_iff_out.mp rfl
  have h1 : (Quotient.out (mk (abv' a))) ≈ (abv' a) := h a
  have h2 :  (abv' b) ≈ (Quotient.out (mk (abv' b))) := by exact Quotient.mk_eq_iff_out.mp rfl
  apply Setoid.trans h1 (Setoid.trans _ h2)
  intro e he
  specialize hab e he
  rcases hab with ⟨i, hi⟩
  use i
  intro j hj
  specialize hi j hj
  refine abs_sub_lt_iff.mpr ?_
  simp only [sub_apply] at hi
  have h3 : abv (a j) - abv (b j) < e := lt_of_le_of_lt (IsAbsoluteValue.sub_abv_le_abv_sub abv (a j) (b j)) hi
  have h3' : abv (b j) - abv (a j) < e := by
    rw [IsAbsoluteValue.abv_sub abv] at hi
    exact lt_of_le_of_lt (IsAbsoluteValue.sub_abv_le_abv_sub abv (b j) (a j)) hi
  exact ⟨h3, h3'⟩

def LE_compl :  (Cauchy (fun x : α => |x|)) → (Cauchy (fun x : α => |x|)) → Prop := by
  intro a b

  sorry

instance LE_compl' : LE (Cauchy (fun x : α ↦ |x|)) := by
  refine { le := ?le }
  exact LE_compl

instance b : LinearOrderedField (Cauchy (fun x : α ↦ |x|)) where
  add := fun x y => x + y
  add_assoc :=  add_assoc
  zero := 0
  zero_add := AddRightCancelMonoid.zero_add
  add_zero := AddLeftCancelMonoid.add_zero
  nsmul := fun n a => n • a
  add_comm := AddCommMagma.add_comm
  mul := fun x y => x * y
  left_distrib := LeftDistribClass.left_distrib
  right_distrib := RightDistribClass.right_distrib
  zero_mul := zero_mul
  mul_zero := mul_zero
  mul_assoc := mul_assoc
  one := 1
  one_mul := one_mul
  mul_one := mul_one
  neg := by exact fun a => - a
  zsmul := fun n a => n • a
  neg_add_cancel := neg_add_cancel
  le := LE_compl
  le_refl := _
  le_trans := _
  le_antisymm := _
  add_le_add_left := _
  exists_pair_ne := _
  zero_le_one := _
  mul_pos := _
  le_total := _
  decidableLE := _
  mul_comm := _
  inv := _
  mul_inv_cancel := _
  inv_zero := _
  nnqsmul := _
  qsmul := _

def aabs : AbsoluteValue (CauSeq.Completion.Cauchy abv) (CauSeq.Completion.Cauchy (fun x : α ↦ |x|)) := by sorry

instance aux (aabs : AbsoluteValue (CauSeq.Completion.Cauchy abv) (CauSeq.Completion.Cauchy (fun x : α ↦ |x|))) : IsAbsoluteValue aabs where
  abv_nonneg' := AbsoluteValue.nonneg aabs
  abv_eq_zero' := AbsoluteValue.eq_zero aabs
  abv_add' := AbsoluteValue.add_le aabs
  abv_mul' := AbsoluteValue.map_mul aabs
