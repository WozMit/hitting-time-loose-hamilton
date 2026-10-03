module

public import HittingTimeLooseHamilton.CycleSurgery

public section

/-! # Oriented-slot compatibility of local surgery

The surgery constructions preserve the cyclic orientation.  These lemmas expose
that fact without imposing any orientation on the counted, unoriented edge sets.
-/
noncomputable section
namespace LooseHamilton
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace MixedCycleOnWitness
variable {r : ℕ} {S : Finset V} {markers edges : Finset (Finset V)}

theorem contract_old_marker_start (C : MixedCycleOnWitness r S markers edges) (e : ↥edges)
    (hp : C.endpointPair e ∉ markers)
    (hm : ((insert (C.endpointPair e) markers : Finset (Finset V)) : Set (Finset V)).PairwiseDisjoint id)
    (m : ↥markers) :
    (C.contract e hp hm).junction
      ((C.contract e hp hm).slot.symm (.inl ⟨m.val, mem_insert_of_mem m.property⟩)) =
    C.junction (C.slot.symm (.inl m)) := by
  have hs : (C.contract e hp hm).slot.symm (.inl ⟨m.val, mem_insert_of_mem m.property⟩) =
      C.slot.symm (.inl m) := by
    apply (C.contract e hp hm).slot.injective
    rw [Equiv.apply_symm_apply]
    change _ = slotTransfer markers edges (C.endpointPair e) e.val hp e.property
      (C.slot (C.slot.symm (.inl m)))
    rw [Equiv.apply_symm_apply]
    rfl
  exact congrArg C.junction hs

theorem contract_new_marker_start (C : MixedCycleOnWitness r S markers edges) (e : ↥edges)
    (hp : C.endpointPair e ∉ markers)
    (hm : ((insert (C.endpointPair e) markers : Finset (Finset V)) : Set (Finset V)).PairwiseDisjoint id) :
    (C.contract e hp hm).junction
      ((C.contract e hp hm).slot.symm (.inl ⟨C.endpointPair e, mem_insert_self _ _⟩)) =
    C.junction (C.slot.symm (.inr e)) := by
  have hs : (C.contract e hp hm).slot.symm (.inl ⟨C.endpointPair e, mem_insert_self _ _⟩) =
      C.slot.symm (.inr e) := by
    apply (C.contract e hp hm).slot.injective
    rw [Equiv.apply_symm_apply]
    change _ = slotTransfer markers edges (C.endpointPair e) e.val hp e.property
      (C.slot (C.slot.symm (.inr e)))
    rw [Equiv.apply_symm_apply]
    simp [slotTransfer]
  exact congrArg C.junction hs

theorem expand_old_marker_start (C : MixedCycleOnWitness r S markers edges) (p : ↥markers)
    (P : Finset V) (hP : P.card = r - 2) (hPS : Disjoint P S)
    (hE : p.val ∪ P ∉ edges) (m : ↥markers) (hmp : m.val ≠ p.val) :
    (C.expand p P hP hPS hE).junction
      ((C.expand p P hP hPS hE).slot.symm
        (.inl ⟨m.val, mem_erase.mpr ⟨hmp,m.property⟩⟩)) =
    C.junction (C.slot.symm (.inl m)) := by
  have hs : (C.expand p P hP hPS hE).slot.symm (.inl ⟨m.val, mem_erase.mpr ⟨hmp,m.property⟩⟩) =
      C.slot.symm (.inl m) := by
    apply (C.expand p P hP hPS hE).slot.injective
    rw [Equiv.apply_symm_apply]
    change _ = (Equiv.sumComm _ _) (slotTransfer edges markers (p.val ∪ P) p.val hE p.property
      ((Equiv.sumComm _ _) (C.slot (C.slot.symm (.inl m)))))
    rw [Equiv.apply_symm_apply]
    simp [slotTransfer, show m ≠ p from fun h => hmp (congrArg Subtype.val h)]
  exact congrArg C.junction hs

theorem expand_new_ordinary_start (C : MixedCycleOnWitness r S markers edges) (p : ↥markers)
    (P : Finset V) (hP : P.card = r - 2) (hPS : Disjoint P S)
    (hE : p.val ∪ P ∉ edges) :
    (C.expand p P hP hPS hE).junction
      ((C.expand p P hP hPS hE).slot.symm
        (.inr ⟨p.val ∪ P, mem_insert_self _ _⟩)) =
    C.junction (C.slot.symm (.inl p)) := by
  have hs : (C.expand p P hP hPS hE).slot.symm (.inr ⟨p.val ∪ P, mem_insert_self _ _⟩) =
      C.slot.symm (.inl p) := by
    apply (C.expand p P hP hPS hE).slot.injective
    rw [Equiv.apply_symm_apply]
    change _ = (Equiv.sumComm _ _) (slotTransfer edges markers (p.val ∪ P) p.val hE p.property
      ((Equiv.sumComm _ _) (C.slot (C.slot.symm (.inl p)))))
    rw [Equiv.apply_symm_apply]
    simp [slotTransfer]
  exact congrArg C.junction hs
end MixedCycleOnWitness
end LooseHamilton
