module

public import HittingTimeLooseHamilton.PermutationCycle
public import HittingTimeLooseHamilton.EnumerationBridge

public section

/-! # Observable ordinary slots of decoded cycle witnesses -/
noncomputable section
namespace LooseHamilton.PermutationCycleData
open Finset
variable {V A I : Type*} [Fintype V] [DecidableEq V]
  [Fintype A] [DecidableEq A] [Fintype I] [DecidableEq I]
variable {r : ℕ} {markers : Finset (Finset V)}

/-- The witness position of a decoded ordinary edge is its original labelled slot. -/
theorem witness_ordinary_slot (D : PermutationCycleData r markers A I) (hr : 3 ≤ r)
    (i : I) :
    (D.witness hr).slot.symm (.inr (D.expanded.edgeEquiv hr i)) =
      D.expanded.slot.symm (.inr i) := by
  apply (D.witness hr).slot.injective
  rw [Equiv.apply_symm_apply]
  change _ = (Equiv.sumCongr (Equiv.refl _) (D.expanded.edgeEquiv hr))
    (D.expanded.slot (D.expanded.slot.symm (.inr i)))
  rw [Equiv.apply_symm_apply]
  rfl

/-- Starting endpoint of the ordinary edge at label i. -/
theorem witness_ordinary_start (D : PermutationCycleData r markers A I) (hr : 3 ≤ r)
    (i : I) :
    (D.witness hr).junction
      ((D.witness hr).slot.symm (.inr (D.expanded.edgeEquiv hr i))) =
        D.junction (D.slot.symm (.inr i)) := by
  rw [D.witness_ordinary_slot hr i]
  change D.junction ((BlockEnumeration.cycleTraversal D.successor D.cyclic D.root)
    ((BlockEnumeration.cycleTraversal D.successor D.cyclic D.root).symm
      (D.slot.symm (.inr i)))) = _
  rw [Equiv.apply_symm_apply]

/-- Ending endpoint of the ordinary edge at label i. -/
theorem witness_ordinary_end (D : PermutationCycleData r markers A I) (hr : 3 ≤ r)
    (i : I) :
    (D.witness hr).junction (finRotate (D.witness hr).length
      ((D.witness hr).slot.symm (.inr (D.expanded.edgeEquiv hr i)))) =
        D.junction (D.successor (D.slot.symm (.inr i))) := by
  rw [D.witness_ordinary_slot hr i]
  change D.junction ((BlockEnumeration.cycleTraversal D.successor D.cyclic D.root)
    (finRotate _ ((BlockEnumeration.cycleTraversal D.successor D.cyclic D.root).symm
      (D.slot.symm (.inr i))))) = _
  rw [BlockEnumeration.cycleTraversal_rotate, Equiv.apply_symm_apply]

/-- Private blocks are not changed when the labels are forgotten. -/
theorem witness_privateBlock (D : PermutationCycleData r markers A I) (hr : 3 ≤ r)
    (i : I) :
    (D.witness hr).privateBlock (D.expanded.edgeEquiv hr i) = D.privateBlock i := by
  change D.expanded.privateBlock ((D.expanded.edgeEquiv hr).symm
    (D.expanded.edgeEquiv hr i)) = _
  rw [Equiv.symm_apply_apply]
  rfl

/-- Starting endpoint of a decoded marked slot. -/
theorem witness_marker_start (D : PermutationCycleData r markers A I) (hr : 3 ≤ r)
    (e : ↥markers) :
    ((D.witness hr).markerStart e).val = D.junction (D.slot.symm (.inl e)) := by
  change D.expanded.junction
    ((D.expanded.slot.trans (Equiv.sumCongr (Equiv.refl _) (D.expanded.edgeEquiv hr))).symm
      (.inl e)) = _
  simpa using D.expanded_marker_start e

/-- Ending endpoint of a decoded marked slot. -/
theorem witness_marker_end (D : PermutationCycleData r markers A I) (hr : 3 ≤ r)
    (e : ↥markers) :
    (D.witness hr).junction (finRotate (D.witness hr).length
      ((D.witness hr).slot.symm (.inl e))) =
        D.junction (D.successor (D.slot.symm (.inl e))) := by
  change D.junction ((BlockEnumeration.cycleTraversal D.successor D.cyclic D.root)
    (finRotate _ ((BlockEnumeration.cycleTraversal D.successor D.cyclic D.root).symm
      (D.slot.symm (.inl e))))) = _
  rw [BlockEnumeration.cycleTraversal_rotate, Equiv.apply_symm_apply]

end LooseHamilton.PermutationCycleData
