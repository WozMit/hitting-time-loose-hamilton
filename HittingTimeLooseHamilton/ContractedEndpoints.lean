module

public import HittingTimeLooseHamilton.PermutationTransport

public section
noncomputable section
open Finset
namespace LooseHamilton.MixedCycleWitness
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {r : ℕ} {markers edges : Finset (Finset V)}

/-- Initial junction of a contracted block. -/
@[expose] def blockStart (C : MixedCycleWitness r markers edges) : C.ContractedBlock → V
  | .inl m => (C.markerStart m).val
  | .inr v => v.val

/-- Final junction of a contracted block. -/
@[expose] def blockEnd (C : MixedCycleWitness r markers edges) : C.ContractedBlock → V
  | .inl m => C.junction (finRotate C.length (C.slot.symm (.inl m)))
  | .inr v => v.val

@[simp] theorem blockEnd_eq (C : MixedCycleWitness r markers edges) (b : C.ContractedBlock) :
    C.blockEnd b = C.junction (C.outgoingSlot b) := by
  cases b with
  | inl m => rfl
  | inr v => exact (C.junction_ordinaryJunctionIndex v).symm

@[simp] theorem ordinary_slot_index (C : MixedCycleWitness r markers edges)
    (b : C.ContractedBlock) :
    C.slot.symm (.inr (C.outgoingEdge b)) = C.outgoingSlot b := by
  rw [← C.slot_outgoingEdge, C.slot.symm_apply_apply]

/-- The next contracted block starts where the current ordinary edge ends. -/
theorem blockSuccessor_start (C : MixedCycleWitness r markers edges) (b : C.ContractedBlock) :
    C.blockStart (C.blockSuccessor b) =
      C.junction (finRotate C.length (C.outgoingSlot b)) := by
  let i := C.outgoingSlot b
  have hi : C.slot.symm (.inr (C.outgoingEdge b)) = i := C.ordinary_slot_index b
  cases hn : C.slot (finRotate C.length i) with
  | inl m =>
    have hm : C.mixedSuccessor (.inl (C.outgoingEdge b)) = .inr m := by
      change (C.slot (finRotate C.length (C.slot.symm (.inr (C.outgoingEdge b))))).swap = _
      rw [hi, hn]; rfl
    have hf : C.mixedSuccessor (.inr m) = .inl (C.outgoingEdge (.inl m)) := by
      change (C.slot (C.outgoingSlot (.inl m))).swap = _
      rw [C.slot_outgoingEdge]; rfl
    have hs : C.ordinarySuccessor (C.outgoingEdge b) = C.outgoingEdge (.inl m) :=
      BlockEnumeration.skipNext_through C.mixedSuccessor_separated hm hf
    have hb : C.blockSuccessor b = .inl m := by
      change C.blockEdgeEquiv.symm (C.ordinarySuccessor (C.blockEdgeEquiv b)) = _
      change C.blockEdgeEquiv.symm (C.ordinarySuccessor (C.outgoingEdge b)) = _
      rw [hs]
      exact C.blockEdgeEquiv.symm_apply_apply (.inl m)
    rw [hb]
    change C.junction (C.slot.symm (.inl m)) = _
    congr 1
    exact C.slot.symm_apply_eq.mpr hn.symm
  | inr f =>
    have hm : C.mixedSuccessor (.inl (C.outgoingEdge b)) = .inl f := by
      change (C.slot (finRotate C.length (C.slot.symm (.inr (C.outgoingEdge b))))).swap = _
      rw [hi, hn]; rfl
    have hs : C.ordinarySuccessor (C.outgoingEdge b) = f :=
      BlockEnumeration.skipNext_direct C.mixedSuccessor_separated hm
    have hb : C.blockSuccessor b = C.blockEdgeEquiv.symm f := by
      change C.blockEdgeEquiv.symm (C.ordinarySuccessor (C.outgoingEdge b)) = _
      rw [hs]
    rw [hb]
    generalize hx : C.blockEdgeEquiv.symm f = x
    have hxf : C.outgoingEdge x = f := by
      change C.blockEdgeEquiv x = f
      rw [← hx, C.blockEdgeEquiv.apply_symm_apply]
    have hslot : C.outgoingSlot x = finRotate C.length i := by
      apply C.slot.injective
      rw [C.slot_outgoingEdge, hxf, hn]
    cases x with
    | inl m =>
      have hprev : C.slot.symm (.inl m) = i := (finRotate C.length).injective hslot
      have hbad : Sum.inl m = Sum.inr (C.outgoingEdge b) := by
        rw [← C.slot.apply_symm_apply (.inl m), hprev]
        exact C.slot_outgoingEdge b
      cases hbad
    | inr v =>
      change v.val = _
      rw [← C.junction_ordinaryJunctionIndex v]
      exact congrArg C.junction hslot

/-- Recover every ordinary edge from its block endpoints and its private vertices. -/
theorem outgoingEdge_formula (C : MixedCycleWitness r markers edges) (b : C.ContractedBlock) :
    (C.outgoingEdge b).val =
      {C.blockEnd b, C.blockStart (C.blockSuccessor b)} ∪ C.privateBlock (C.outgoingEdge b) := by
  have he := C.slot_edge (C.outgoingSlot b)
  rw [C.slot_outgoingEdge] at he
  simp only at he
  rw [C.blockEnd_eq, C.blockSuccessor_start]
  exact he

end LooseHamilton.MixedCycleWitness
