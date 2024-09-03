import Mathlib.Algebra.Order.CauSeq.Completion
--import Mathlib

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

private irreducible_def lt : Cauchy (fun r : α ↦ |r|) → Cauchy (fun r : α ↦ |r|) → Prop := by
  intro a b
  apply Quotient.liftOn₂ a b (· < ·)
  intro a₁ b₁ a₂ b₂ ha hb
  simp only [eq_iff_iff]
  sorry

instance : LT (Cauchy (fun r : α ↦ |r|)) :=
  ⟨lt⟩
private irreducible_def le (x y : (Cauchy (fun r : α ↦ |r|))) : Prop :=
  x < y ∨ x = y

instance : LE (Cauchy (fun r : α ↦ |r|)) :=
  ⟨le⟩

instance partialOrder : PartialOrder (Cauchy (fun r : α ↦ |r|)) where
  le := (· ≤ ·)
  lt := (· < ·)
  lt_iff_le_not_le a b := by sorry
    /- induction' a using Real.ind_mk with a
    induction' b using Real.ind_mk with b
    simpa using lt_iff_le_not_le -/
  le_refl a := by sorry
    /- induction' a using Real.ind_mk with a
    rw [mk_le] -/
  le_trans a b c := by sorry
    /- induction' a using Real.ind_mk with a
    induction' b using Real.ind_mk with b
    induction' c using Real.ind_mk with c
    simpa using le_trans -/
  le_antisymm a b := by sorry
    /- induction' a using Real.ind_mk with a
    induction' b using Real.ind_mk with b
    simpa [mk_eq] using @CauSeq.le_antisymm _ _ a b -/
/-
  | ⟨x⟩, ⟨y⟩ =>
    (Quotient.liftOn₂ x y (· < ·)) fun _ _ _ _ hf hg =>
      propext <|
        ⟨fun h => lt_of_eq_of_lt (Setoid.symm hf) (lt_of_lt_of_eq h hg), fun h =>
          lt_of_eq_of_lt hf (lt_of_lt_of_eq h (Setoid.symm hg))⟩
 -/

/- def LE_compl :  (Cauchy (fun x : α => |x|)) → (Cauchy (fun x : α => |x|)) → Prop := by
  intro a b

  sorry

instance LE_compl' : LE (Cauchy (fun x : α ↦ |x|)) := by
  refine { le := ?le }
  exact LE_compl -/
set_option diagnostics true

noncomputable instance b : LinearOrderedField (Cauchy (fun x : α ↦ |x|)) := by infer_instance

/- noncomputable instance b : LinearOrderedField (Cauchy (fun x : α ↦ |x|)) where
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
  neg := fun a => - a
  zsmul := fun n a => n • a
  neg_add_cancel := neg_add_cancel
  le := le
  le_refl := Preorder.le_refl
  le_trans := Preorder.le_trans
  le_antisymm := partialOrder.le_antisymm
  add_le_add_left := by sorry
  exists_pair_ne := by sorry
  zero_le_one := by sorry
  mul_pos := by sorry
  le_total := by sorry
  decidableLE := by exact Classical.decRel fun x1 x2 => x1 ≤ x2
  mul_comm := CommMonoid.mul_comm
  inv := by exact fun a => a⁻¹
  mul_inv_cancel := by exact fun a a_1 => Completion.mul_inv_cancel a_1
  inv_zero := inv_zero
  nnqsmul := fun n a => n • a
  qsmul := fun n a => n • a

def aabs : AbsoluteValue (CauSeq.Completion.Cauchy abv) (CauSeq.Completion.Cauchy (fun x : α ↦ |x|)) := by sorry

instance aux (aabs : AbsoluteValue (CauSeq.Completion.Cauchy abv) (CauSeq.Completion.Cauchy (fun x : α ↦ |x|))) : IsAbsoluteValue aabs where
  abv_nonneg' := AbsoluteValue.nonneg aabs
  abv_eq_zero' := AbsoluteValue.eq_zero aabs
  abv_add' := AbsoluteValue.add_le aabs
  abv_mul' := AbsoluteValue.map_mul aabs
 -/
