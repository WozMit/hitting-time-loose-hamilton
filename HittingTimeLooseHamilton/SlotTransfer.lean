module

public import HittingTimeLooseHamilton.Cycles

public section
noncomputable section
namespace LooseHamilton
variable {V : Type*} [DecidableEq V]
/-- Move one distinguished object from the right slot family to a fresh left slot. -/
@[expose] def slotTransfer (A B : Finset V) (p e : V) (hp : p ∉ A) (he : e ∈ B) :
    (↥A ⊕ ↥B) ≃ (↥(insert p A) ⊕ ↥(B.erase e)) where
  toFun x := match x with
    | .inl a => .inl ⟨a, Finset.mem_insert_of_mem a.property⟩
    | .inr b => if h : b.val = e then .inl ⟨p, Finset.mem_insert_self _ _⟩
      else .inr ⟨b, Finset.mem_erase.mpr ⟨h, b.property⟩⟩
  invFun x := match x with
    | .inl a => if h : a.val = p then .inr ⟨e, he⟩
      else .inl ⟨a, (Finset.mem_insert.mp a.property).resolve_left h⟩
    | .inr b => .inr ⟨b, (Finset.mem_erase.mp b.property).2⟩
  left_inv x := by
    cases x with
    | inl a =>
      have h : a.val ≠ p := by intro h; exact hp (h ▸ a.property)
      simp [h]
    | inr b =>
      by_cases h : b.val = e
      · simp [h]; exact Subtype.ext h.symm
      · simp [h]
  right_inv x := by
    cases x with
    | inl a =>
      by_cases h : a.val = p
      · simp [h]; exact Subtype.ext h.symm
      · simp [h]
    | inr b =>
      have h := (Finset.mem_erase.mp b.property).1
      simp [h]
end LooseHamilton
