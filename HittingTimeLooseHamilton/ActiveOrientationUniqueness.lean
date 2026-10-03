module

public import HittingTimeLooseHamilton.OrientationUniqueness
public import HittingTimeLooseHamilton.VertexRestriction

public section

/-! Orientation uniqueness on an arbitrary active vertex set. -/
noncomputable section
open Finset
namespace LooseHamilton.MixedCycleOnWitness
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {r : ℕ} {S : Finset V} {markers edges : Finset (Finset V)}

private def restrictedLabel (C : MixedCycleOnWitness r S markers edges)
    (e : ↥markers ⊕ ↥edges) : ↥(restrictEdges S markers) ⊕ ↥(restrictEdges S edges) :=
  (Equiv.sumCongr
    (restrictedEdgeEquiv S markers (fun _ h => C.marked_subset_active h))
    (restrictedEdgeEquiv S edges (fun _ h => C.edge_subset_active h))) e

private theorem restrictedLabel_eq (C D : MixedCycleOnWitness r S markers edges)
    (e : ↥markers ⊕ ↥edges) : C.restrictedLabel e = D.restrictedLabel e := by
  cases e <;> rfl

private theorem restrict_slot (C : MixedCycleOnWitness r S markers edges)
    (e : ↥markers ⊕ ↥edges) :
    C.restrict.slot.symm (C.restrictedLabel e) = C.slot.symm e := by
  apply C.restrict.slot.injective
  rw [Equiv.apply_symm_apply]
  change C.restrictedLabel e = C.restrictedLabel (C.slot (C.slot.symm e))
  rw [C.slot.apply_symm_apply]

/-- A common direction of one marked edge fixes the start of every mixed edge. -/
theorem slot_start_eq_of_root (C D : MixedCycleOnWitness r S markers edges) (hr : 3 ≤ r)
    (root : ↥markers)
    (hroot : C.junction (C.slot.symm (.inl root)) =
      D.junction (D.slot.symm (.inl root)))
    (e : ↥markers ⊕ ↥edges) :
    C.junction (C.slot.symm e) = D.junction (D.slot.symm e) := by
  let root' : ↥(restrictEdges S markers) :=
    restrictedEdgeEquiv S markers (fun _ h => C.marked_subset_active h) root
  have hroot' : C.restrict.markerStart root' = D.restrict.markerStart root' := by
    apply Subtype.ext
    apply Subtype.ext
    change (C.restrict.junction (C.restrict.slot.symm (C.restrictedLabel (.inl root)))).val =
      (D.restrict.junction (D.restrict.slot.symm (D.restrictedLabel (.inl root)))).val
    rw [C.restrict_slot, D.restrict_slot]
    exact hroot
  have hh := C.restrict.slot_start_eq_of_root D.restrict hr root' hroot'
    (C.restrictedLabel e)
  rw [C.restrictedLabel_eq D e] at hh
  rw [← C.restrictedLabel_eq D e, C.restrict_slot] at hh
  rw [C.restrictedLabel_eq D e, D.restrict_slot] at hh
  exact congrArg Subtype.val hh

/-- A common root direction also fixes every terminal junction. -/
theorem slot_end_eq_of_root (C D : MixedCycleOnWitness r S markers edges) (hr : 3 ≤ r)
    (root : ↥markers)
    (hroot : C.junction (C.slot.symm (.inl root)) =
      D.junction (D.slot.symm (.inl root)))
    (e : ↥markers ⊕ ↥edges) :
    C.junction (finRotate C.length (C.slot.symm e)) =
      D.junction (finRotate D.length (D.slot.symm e)) := by
  let root' : ↥(restrictEdges S markers) :=
    restrictedEdgeEquiv S markers (fun _ h => C.marked_subset_active h) root
  have hroot' : C.restrict.markerStart root' = D.restrict.markerStart root' := by
    apply Subtype.ext
    apply Subtype.ext
    change (C.restrict.junction (C.restrict.slot.symm (C.restrictedLabel (.inl root)))).val =
      (D.restrict.junction (D.restrict.slot.symm (D.restrictedLabel (.inl root)))).val
    rw [C.restrict_slot, D.restrict_slot]
    exact hroot
  have hh := C.restrict.slot_end_eq_of_root D.restrict hr root' hroot'
    (C.restrictedLabel e)
  rw [C.restrict_slot] at hh
  rw [C.restrictedLabel_eq D e, D.restrict_slot] at hh
  exact congrArg Subtype.val hh

/-- Under the common root direction there is only one outgoing mixed edge at a junction. -/
theorem slot_label_eq_of_start (C D : MixedCycleOnWitness r S markers edges) (hr : 3 ≤ r)
    (root : ↥markers)
    (hroot : C.junction (C.slot.symm (.inl root)) =
      D.junction (D.slot.symm (.inl root)))
    (e f : ↥markers ⊕ ↥edges)
    (h : C.junction (C.slot.symm e) = D.junction (D.slot.symm f)) : e = f := by
  apply C.slot.symm.injective
  apply C.junction_injective
  exact h.trans (C.slot_start_eq_of_root D hr root hroot f).symm

/-- Under the common root direction there is only one incoming mixed edge at a junction. -/
theorem slot_label_eq_of_end (C D : MixedCycleOnWitness r S markers edges) (hr : 3 ≤ r)
    (root : ↥markers)
    (hroot : C.junction (C.slot.symm (.inl root)) =
      D.junction (D.slot.symm (.inl root)))
    (e f : ↥markers ⊕ ↥edges)
    (h : C.junction (finRotate C.length (C.slot.symm e)) =
      D.junction (finRotate D.length (D.slot.symm f))) : e = f := by
  apply C.slot.symm.injective
  apply (finRotate C.length).injective
  apply C.junction_injective
  exact h.trans (C.slot_end_eq_of_root D hr root hroot f).symm

end LooseHamilton.MixedCycleOnWitness
