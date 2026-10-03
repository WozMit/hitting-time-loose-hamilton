module

public import HittingTimeLooseHamilton.OrientationUniqueness
public import HittingTimeLooseHamilton.ContractedEndpoints

public section
noncomputable section
namespace LooseHamilton.MixedCycleWitness
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {r : ℕ} {markers edges edges' : Finset (Finset V)}

/-- The physical starting junction determines an outgoing edge in a fixed orientation. -/
theorem physical_outgoingEdge (C : MixedCycleWitness r markers edges)
    (D : MixedCycleWitness r markers edges') (he : edges = edges') (hr : 3 ≤ r)
    (root : ↥markers) (hroot : C.markerStart root = D.markerStart root)
    (b : C.ContractedBlock) (d : D.ContractedBlock)
    (hend : C.blockEnd b = D.blockEnd d) :
    (C.outgoingEdge b).val = (D.outgoingEdge d).val := by
  subst edges'
  have hs := C.slot_start_eq_of_root D hr root hroot (.inr (D.outgoingEdge d))
  have hc : C.junction (C.slot.symm (.inr (C.outgoingEdge b))) =
      C.junction (C.slot.symm (.inr (D.outgoingEdge d))) := by
    rw [C.ordinary_slot_index, ← C.blockEnd_eq, hend, D.blockEnd_eq,
      ← D.ordinary_slot_index]
    exact hs.symm
  exact congrArg Subtype.val (Sum.inr_injective (C.slot.symm.injective (C.junction_injective hc)))

/-- The ending junction is likewise intrinsic to the physical outgoing edge. -/
theorem physical_next_junction (C : MixedCycleWitness r markers edges)
    (D : MixedCycleWitness r markers edges') (he : edges = edges') (hr : 3 ≤ r)
    (root : ↥markers) (hroot : C.markerStart root = D.markerStart root)
    (b : C.ContractedBlock) (d : D.ContractedBlock)
    (hend : C.blockEnd b = D.blockEnd d) :
    C.junction (finRotate C.length (C.outgoingSlot b)) =
      D.junction (finRotate D.length (D.outgoingSlot d)) := by
  subst edges'
  have heq : C.outgoingEdge b = D.outgoingEdge d :=
    Subtype.ext (C.physical_outgoingEdge D rfl hr root hroot b d hend)
  rw [← C.ordinary_slot_index, ← D.ordinary_slot_index, heq]
  exact C.slot_end_eq_of_root D hr root hroot (.inr (D.outgoingEdge d))

/-- Private vertices depend on the physical edge, not its presentation. -/
theorem physical_privateBlock (C : MixedCycleWitness r markers edges)
    (D : MixedCycleWitness r markers edges') (he : edges = edges') (hr : 3 ≤ r)
    (root : ↥markers) (hroot : C.markerStart root = D.markerStart root)
    (b : C.ContractedBlock) (d : D.ContractedBlock)
    (hend : C.blockEnd b = D.blockEnd d) :
    C.privateBlock (C.outgoingEdge b) = D.privateBlock (D.outgoingEdge d) := by
  subst edges'
  have heq : C.outgoingEdge b = D.outgoingEdge d :=
    Subtype.ext (C.physical_outgoingEdge D rfl hr root hroot b d hend)
  rw [heq]
  exact C.privateBlock_eq D hr _
end LooseHamilton.MixedCycleWitness
