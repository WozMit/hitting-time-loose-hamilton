module

public import HittingTimeLooseHamilton.SlotTransfer

public section
noncomputable section
namespace LooseHamilton
open Finset
variable {α : Type*} [DecidableEq α]

@[expose] def replaceInsertedEquiv (M : Finset α) (p q : α) (hp : p ∉ M) (hq : q ∉ M) :
    ↥(insert p M) ≃ ↥(insert q M) :=
  (subtypeInsertEquivOption hp).trans (subtypeInsertEquivOption hq).symm

@[simp] theorem replaceInsertedEquiv_new (M : Finset α) (p q : α)
    (hp : p ∉ M) (hq : q ∉ M) :
    replaceInsertedEquiv M p q hp hq ⟨p, mem_insert_self p M⟩ =
      ⟨q, mem_insert_self q M⟩ := by
  simp [replaceInsertedEquiv, subtypeInsertEquivOption]

@[simp] theorem replaceInsertedEquiv_old (M : Finset α) (p q : α)
    (hp : p ∉ M) (hq : q ∉ M) (a : ↥M) :
    replaceInsertedEquiv M p q hp hq ⟨a, mem_insert_of_mem a.property⟩ =
      ⟨a, mem_insert_of_mem a.property⟩ := by
  have h : a.val ≠ p := fun h => hp (h ▸ a.property)
  simp [replaceInsertedEquiv, subtypeInsertEquivOption, h]

@[expose] def edgeInsertEquiv (E : Finset α) (e : α) (he : e ∉ E) :
    (↥E ⊕ Fin 1) ≃ ↥(insert e E) where
  toFun s := match s with
    | .inl a => ⟨a, mem_insert_of_mem a.property⟩
    | .inr _ => ⟨e, mem_insert_self e E⟩
  invFun a := if h : a.val = e then .inr 0
    else .inl ⟨a, (mem_insert.mp a.property).resolve_left h⟩
  left_inv s := by
    cases s with
    | inl a =>
      have h : a.val ≠ e := fun h => he (h ▸ a.property)
      simp [h]
    | inr i => simp; exact Subsingleton.elim _ _
  right_inv a := by
    by_cases h : a.val = e
    · simp [h]; exact Subtype.ext h.symm
    · simp [h]

@[simp] theorem edgeInsertEquiv_old (E : Finset α) (e : α) (he : e ∉ E) (a : ↥E) :
    edgeInsertEquiv E e he (.inl a) = ⟨a, mem_insert_of_mem a.property⟩ := rfl
@[simp] theorem edgeInsertEquiv_new (E : Finset α) (e : α) (he : e ∉ E) (i : Fin 1) :
    edgeInsertEquiv E e he (.inr i) = ⟨e, mem_insert_self e E⟩ := rfl

@[expose] def spliceSlotsI (M E : Finset α) (p q e : α)
    (hp : p ∉ M) (hq : q ∉ M) (he : e ∉ E) :
    ((↥(insert p M) ⊕ ↥E) ⊕ Fin 1) ≃
      (↥(insert q M) ⊕ ↥(insert e E)) :=
  (Equiv.sumAssoc _ _ _).trans
    (Equiv.sumCongr (replaceInsertedEquiv M p q hp hq) (edgeInsertEquiv E e he))

@[simp] theorem spliceSlotsI_marker (M E : Finset α) (p q e : α)
    (hp : p ∉ M) (hq : q ∉ M) (he : e ∉ E) (a : ↥(insert p M)) :
    spliceSlotsI M E p q e hp hq he (.inl (.inl a)) =
      .inl (replaceInsertedEquiv M p q hp hq a) := rfl
@[simp] theorem spliceSlotsI_edge (M E : Finset α) (p q e : α)
    (hp : p ∉ M) (hq : q ∉ M) (he : e ∉ E) (a : ↥E) :
    spliceSlotsI M E p q e hp hq he (.inl (.inr a)) =
      .inr ⟨a, mem_insert_of_mem a.property⟩ := rfl
@[simp] theorem spliceSlotsI_new (M E : Finset α) (p q e : α)
    (hp : p ∉ M) (hq : q ∉ M) (he : e ∉ E) (i : Fin 1) :
    spliceSlotsI M E p q e hp hq he (.inr i) =
      .inr ⟨e, mem_insert_self e E⟩ := rfl

/-- Reorder three newly inserted slots: first edge, marker, second edge. -/
@[expose] def threeSlotShuffle (A B : Type*) :
    ((A ⊕ B) ⊕ Fin 3) ≃ ((A ⊕ Fin 1) ⊕ ((B ⊕ Fin 1) ⊕ Fin 1)) where
  toFun s := match s with
    | .inl (.inl a) => .inl (.inl a)
    | .inl (.inr b) => .inr (.inl (.inl b))
    | .inr i => if i = 0 then .inr (.inr 0)
        else if i = 1 then .inl (.inr 0) else .inr (.inl (.inr 0))
  invFun s := match s with
    | .inl (.inl a) => .inl (.inl a)
    | .inl (.inr _) => .inr 1
    | .inr (.inl (.inl b)) => .inl (.inr b)
    | .inr (.inl (.inr _)) => .inr 2
    | .inr (.inr _) => .inr 0
  left_inv s := by
    rcases s with ((a | b) | i)
    · rfl
    · rfl
    · fin_cases i <;> simp
  right_inv s := by
    rcases s with ((a | i) | ((b | j) | k))
    · rfl
    · fin_cases i; rfl
    · rfl
    · fin_cases j; rfl
    · fin_cases k; rfl

/-- Type II splice slots; the two inserted edges remain ordered by their role. -/
@[expose] def spliceSlotsII (M E : Finset α) (p q o e₁ e₂ : α)
    (hp : p ∉ M) (hq : q ∉ M) (ho : o ∉ insert q M)
    (he₂ : e₂ ∉ E) (he₁ : e₁ ∉ insert e₂ E) :
    ((↥(insert p M) ⊕ ↥E) ⊕ Fin 3) ≃
      (↥(insert q (insert o M)) ⊕ ↥(insert e₁ (insert e₂ E))) :=
  (threeSlotShuffle _ _).trans (Equiv.sumCongr
    (((Equiv.sumCongr (replaceInsertedEquiv M p q hp hq) (Equiv.refl _)).trans
      (edgeInsertEquiv (insert q M) o ho)).trans
        (Equiv.subtypeEquivRight (fun _ => by rw [insert_comm])))
    ((Equiv.sumCongr (edgeInsertEquiv E e₂ he₂) (Equiv.refl _)).trans
      (edgeInsertEquiv (insert e₂ E) e₁ he₁)))

@[simp] theorem spliceSlotsII_marker (M E : Finset α) (p q o e₁ e₂ : α)
    (hp : p ∉ M) (hq : q ∉ M) (ho : o ∉ insert q M)
    (he₂ : e₂ ∉ E) (he₁ : e₁ ∉ insert e₂ E) (a : ↥(insert p M)) :
    (spliceSlotsII M E p q o e₁ e₂ hp hq ho he₂ he₁ (.inl (.inl a))) =
      .inl ⟨(replaceInsertedEquiv M p q hp hq a).val, by
        rw [insert_comm]; exact mem_insert_of_mem (replaceInsertedEquiv M p q hp hq a).property⟩ := rfl
@[simp] theorem spliceSlotsII_edge (M E : Finset α) (p q o e₁ e₂ : α)
    (hp : p ∉ M) (hq : q ∉ M) (ho : o ∉ insert q M)
    (he₂ : e₂ ∉ E) (he₁ : e₁ ∉ insert e₂ E) (a : ↥E) :
    spliceSlotsII M E p q o e₁ e₂ hp hq ho he₂ he₁ (.inl (.inr a)) =
      .inr ⟨a, mem_insert_of_mem (mem_insert_of_mem a.property)⟩ := rfl
@[simp] theorem spliceSlotsII_zero (M E : Finset α) (p q o e₁ e₂ : α)
    (hp : p ∉ M) (hq : q ∉ M) (ho : o ∉ insert q M)
    (he₂ : e₂ ∉ E) (he₁ : e₁ ∉ insert e₂ E) :
    spliceSlotsII M E p q o e₁ e₂ hp hq ho he₂ he₁ (.inr 0) =
      .inr ⟨e₁, mem_insert_self _ _⟩ := rfl
@[simp] theorem spliceSlotsII_one (M E : Finset α) (p q o e₁ e₂ : α)
    (hp : p ∉ M) (hq : q ∉ M) (ho : o ∉ insert q M)
    (he₂ : e₂ ∉ E) (he₁ : e₁ ∉ insert e₂ E) :
    spliceSlotsII M E p q o e₁ e₂ hp hq ho he₂ he₁ (.inr 1) =
      .inl ⟨o, mem_insert_of_mem (mem_insert_self _ _)⟩ := rfl
@[simp] theorem spliceSlotsII_two (M E : Finset α) (p q o e₁ e₂ : α)
    (hp : p ∉ M) (hq : q ∉ M) (ho : o ∉ insert q M)
    (he₂ : e₂ ∉ E) (he₁ : e₁ ∉ insert e₂ E) :
    spliceSlotsII M E p q o e₁ e₂ hp hq ho he₂ he₁ (.inr 2) =
      .inr ⟨e₂, mem_insert_of_mem (mem_insert_self _ _)⟩ := rfl
end LooseHamilton
