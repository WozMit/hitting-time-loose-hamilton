module

public import HittingTimeLooseHamilton.CycleOnCounting
public import HittingTimeLooseHamilton.DirectedCompletions

public section

/-! Relative directions on an active vertex set, with the host held fixed. -/
noncomputable section
namespace LooseHamilton
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Direction of two markers in an actual cycle on the active vertices. -/
@[expose] def rootedDirectedCycleOn (r : ℕ) (S : Finset V) (markers edges : Finset (Finset V))
    (root distinguished : ↥markers) (a y : V) : Prop :=
  ∃ C : MixedCycleOnWitness r S markers edges,
    C.junction (C.slot.symm (.inl root)) = a ∧
    C.junction (C.slot.symm (.inl distinguished)) = y

/-- A marker transported to the surviving vertex type. -/
@[expose] def activeRestrictedMarker (S : Finset V) {markers : Finset (Finset V)}
    (m : ↥markers) : ↥(restrictEdges S markers) :=
  ⟨restrictEdge S m.val, mem_image_of_mem _ m.property⟩

/-- A prescribed root endpoint transported to the surviving vertex type. -/
@[expose] def activeRestrictedRootPoint (S : Finset V) {markers : Finset (Finset V)}
    (hM : ∀ e ∈ markers, e ⊆ S) (root : ↥markers) (a : ↥root.val) :
    ↥(activeRestrictedMarker S root).val :=
  ⟨⟨a.val, hM _ root.property a.property⟩, (mem_restrictEdge _ _ _).mpr a.property⟩

namespace MixedCycleOnWitness
variable {r : ℕ} {S : Finset V} {markers edges : Finset (Finset V)}

@[simp] theorem restrict_markerStart_val (C : MixedCycleOnWitness r S markers edges)
    (m : ↥markers) :
    ((C.restrict.markerStart (activeRestrictedMarker S m)).val).val =
      C.junction (C.slot.symm (.inl m)) := by
  have hs : C.restrict.slot.symm (.inl (activeRestrictedMarker S m)) =
      C.slot.symm (.inl m) := by
    apply C.restrict.slot.injective
    rw [Equiv.apply_symm_apply]
    change _ = (Equiv.sumCongr
      (restrictedEdgeEquiv S markers (fun _ h => C.marked_subset_active h))
      (restrictedEdgeEquiv S edges (fun _ h => C.edge_subset_active h)))
      (C.slot (C.slot.symm (.inl m)))
    rw [Equiv.apply_symm_apply]
    rfl
  change C.junction (C.restrict.slot.symm (.inl (activeRestrictedMarker S m))) = _
  rw [hs]
end MixedCycleOnWitness

/-- Restriction preserves the two directed marker starts. -/
theorem rootedDirectedCycleOn_restrict {r : ℕ} {S : Finset V}
    {markers edges : Finset (Finset V)} (hM : ∀ e ∈ markers, e ⊆ S)
    (root distinguished : ↥markers) (a : ↥root.val) (y : ↥S)
    (h : rootedDirectedCycleOn r S markers edges root distinguished a.val y.val) :
    rootedDirectedCycle r (restrictEdges S markers) (restrictEdges S edges)
      (activeRestrictedMarker S root) (activeRestrictedMarker S distinguished)
      (activeRestrictedRootPoint S hM root a) y := by
  obtain ⟨C, ha, hy⟩ := h
  refine ⟨C.restrict, ?_, ?_⟩
  · apply Subtype.ext
    apply Subtype.ext
    simpa only [MixedCycleOnWitness.restrict_markerStart_val, activeRestrictedRootPoint] using ha
  · apply Subtype.ext
    simpa only [MixedCycleOnWitness.restrict_markerStart_val] using hy

/-- Active directed completions are actual edge sets, not parametrizations. -/
@[expose] def directedCycleOnFamily (r : ℕ) (S : Finset V) (markers host : Finset (Finset V))
    (root distinguished : ↥markers) (a y : V) : Finset (Finset (Finset V)) := by
  classical
  exact (cycleOnFamily r S markers host).filter
    (fun E => rootedDirectedCycleOn r S markers E root distinguished a y)

@[simp] theorem mem_directedCycleOnFamily (r : ℕ) (S : Finset V)
    (markers host : Finset (Finset V)) (root distinguished : ↥markers)
    (a y : V) (E : Finset (Finset V)) :
    E ∈ directedCycleOnFamily r S markers host root distinguished a y ↔
      E ∈ cycleOnFamily r S markers host ∧
        rootedDirectedCycleOn r S markers E root distinguished a y := by
  simp [directedCycleOnFamily]

namespace MixedCycleWitness
variable {r : ℕ} {S : Finset V} {markers edges : Finset (Finset ↥S)}

@[simp] theorem lift_marker_start (C : MixedCycleWitness r markers edges)
    (m : ↥markers) :
    C.lift.junction (C.lift.slot.symm (.inl (liftedEdgeEquiv S markers m))) =
      (C.markerStart m).val.val := by
  have hs : C.lift.slot.symm (.inl (liftedEdgeEquiv S markers m)) =
      C.slot.symm (.inl m) := by
    apply C.lift.slot.injective
    rw [Equiv.apply_symm_apply]
    change _ = (Equiv.sumCongr (liftedEdgeEquiv S markers) (liftedEdgeEquiv S edges))
      (C.slot (C.slot.symm (.inl m)))
    rw [Equiv.apply_symm_apply]
    rfl
  change (C.junction (C.lift.slot.symm (.inl (liftedEdgeEquiv S markers m)))).val = _
  rw [hs]
  rfl
end MixedCycleWitness

/-- Lifting directed cycles from the surviving type preserves both starts. -/
theorem rootedDirectedCycle_lift {r : ℕ} {S : Finset V}
    {markers edges : Finset (Finset ↥S)}
    (root distinguished : ↥markers) (a : ↥root.val) (y : ↥S)
    (h : rootedDirectedCycle r markers edges root distinguished a y) :
    rootedDirectedCycleOn r S (markers.image (liftEdge S)) (edges.image (liftEdge S))
      (liftedEdgeEquiv S markers root) (liftedEdgeEquiv S markers distinguished)
      a.val.val y.val := by
  obtain ⟨C, ha, hy⟩ := h
  refine ⟨C.lift, ?_, ?_⟩
  · simpa only [MixedCycleWitness.lift_marker_start] using
      congrArg (fun b : ↥root.val => b.val.val) ha
  · simpa only [MixedCycleWitness.lift_marker_start] using congrArg Subtype.val hy

/-- Transport across equal marker and edge families depends only on marker values. -/
theorem rootedDirectedCycleOn_congr {r : ℕ} {S : Finset V}
    {M M' E E' : Finset (Finset V)} (hM : M = M') (hE : E = E')
    (p q : ↥M) (p' q' : ↥M') (hp : p.val = p'.val) (hq : q.val = q'.val)
    (a y : V) :
    rootedDirectedCycleOn r S M E p q a y ↔
      rootedDirectedCycleOn r S M' E' p' q' a y := by
  subst M'; subst E'
  have hp' : p = p' := Subtype.ext hp
  have hq' : q = q' := Subtype.ext hq
  subst p'; subst q'; rfl

/-- The ambient direction condition is exactly the existing direction condition
on the induced vertex type. -/
theorem rootedDirectedCycleOn_iff_restrict {r : ℕ} {S : Finset V}
    {markers edges : Finset (Finset V)} (hM : ∀ e ∈ markers, e ⊆ S)
    (hE : ∀ e ∈ edges, e ⊆ S)
    (root distinguished : ↥markers) (a : ↥root.val) (y : ↥S) :
    rootedDirectedCycleOn r S markers edges root distinguished a.val y.val ↔
    rootedDirectedCycle r (restrictEdges S markers) (restrictEdges S edges)
      (activeRestrictedMarker S root) (activeRestrictedMarker S distinguished)
      (activeRestrictedRootPoint S hM root a) y := by
  constructor
  · exact rootedDirectedCycleOn_restrict hM root distinguished a y
  · intro h
    have hl := rootedDirectedCycle_lift
      (activeRestrictedMarker S root) (activeRestrictedMarker S distinguished)
      (activeRestrictedRootPoint S hM root a) y h
    apply (rootedDirectedCycleOn_congr (liftEdges_restrictEdges S markers hM)
      (liftEdges_restrictEdges S edges hE) _ _ root distinguished ?_ ?_ a.val y.val).mp hl
    · exact lift_restrictEdge S root.val (hM _ root.property)
    · exact lift_restrictEdge S distinguished.val (hM _ distinguished.property)

end LooseHamilton
