module

public import HittingTimeLooseHamilton.OrientationUniqueness
public import HittingTimeLooseHamilton.Counting

public section

/-!
# Relative directions of marked completions

A cycle is counted as an unoriented edge set. Prescribing the initial endpoint
of one fixed marker nevertheless gives every other marker a well-defined
relative direction. The two directions partition the actual cycle family in
an arbitrary host; their cardinalities need not be equal.
-/
noncomputable section
open Finset
namespace LooseHamilton
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The distinguished marker starts at `y` when the root starts at `a`. -/
@[expose] def rootedDirectedCycle (r : ℕ) (markers edges : Finset (Finset V))
    (root distinguished : ↥markers) (a : ↥root.val) (y : V) : Prop :=
  ∃ C : MixedCycleWitness r markers edges,
    C.markerStart root = a ∧ (C.markerStart distinguished).val = y

/-- Relative direction is independent of the witness representing the edge set. -/
theorem rootedDirectedCycle_unique {r : ℕ} {markers edges : Finset (Finset V)}
    (hr : 3 ≤ r) (root distinguished : ↥markers) (a : ↥root.val)
    {y z : V} (hy : rootedDirectedCycle r markers edges root distinguished a y)
    (hz : rootedDirectedCycle r markers edges root distinguished a z) : y = z := by
  obtain ⟨C, hC, hy⟩ := hy
  obtain ⟨D, hD, hz⟩ := hz
  have h := C.slot_start_eq_of_root D hr root (hC.trans hD.symm) (.inl distinguished)
  exact hy.symm.trans (h.trans hz)

/-- Any chosen presentation can be normalized to test the intrinsic direction. -/
theorem rootedDirectedCycle_iff_normalize {r : ℕ} {markers edges : Finset (Finset V)}
    (hr : 3 ≤ r) (C : MixedCycleWitness r markers edges)
    (root distinguished : ↥markers) (a : ↥root.val) (y : V) :
    rootedDirectedCycle r markers edges root distinguished a y ↔
      ((C.normalize root a).markerStart distinguished).val = y := by
  constructor
  · intro h
    exact (rootedDirectedCycle_unique hr root distinguished a h
      ⟨C.normalize root a, C.normalize_markerStart root a, rfl⟩).symm
  · intro h
    exact ⟨C.normalize root a, C.normalize_markerStart root a, h⟩

/-- Every cycle has one of the two relative directions of a pair marker. -/
theorem rootedDirectedCycle_exhaustive {r : ℕ} {markers edges : Finset (Finset V)}
    (root distinguished : ↥markers) (a : ↥root.val) {y z : V}
    (hpair : distinguished.val = {y, z}) (hC : IsMixedCycle r markers edges) :
    rootedDirectedCycle r markers edges root distinguished a y ∨
      rootedDirectedCycle r markers edges root distinguished a z := by
  obtain ⟨C⟩ := hC
  let D := C.normalize root a
  have hd : D.markerStart root = a := C.normalize_markerStart root a
  have hm := (D.markerStart distinguished).property
  simp only [hpair] at hm
  simp only [mem_insert, mem_singleton] at hm
  exact hm.elim (fun h => Or.inl ⟨D, hd, h⟩) (fun h => Or.inr ⟨D, hd, h⟩)

/-- Actual edge-set completions having a prescribed relative direction. -/
@[expose] def directedCycleFamily (r : ℕ) (markers host : Finset (Finset V)) (ports : Finset V)
    (root distinguished : ↥markers) (a : ↥root.val) (y : V) :
    Finset (Finset (Finset V)) := by
  classical
  exact (cycleFamily r markers host ports).filter
    (fun edges => rootedDirectedCycle r markers edges root distinguished a y)

@[simp] theorem mem_directedCycleFamily (r : ℕ) (markers host : Finset (Finset V))
    (ports : Finset V) (root distinguished : ↥markers) (a : ↥root.val) (y : V)
    (edges : Finset (Finset V)) :
    edges ∈ directedCycleFamily r markers host ports root distinguished a y ↔
      edges ∈ cycleFamily r markers host ports ∧
        rootedDirectedCycle r markers edges root distinguished a y := by
  classical
  simp [directedCycleFamily]

/-- The two direction classes cover every completion. -/
theorem directedCycleFamily_union {r : ℕ} {markers host : Finset (Finset V)}
    (ports : Finset V) (root distinguished : ↥markers) (a : ↥root.val) {y z : V}
    (hpair : distinguished.val = {y, z}) :
    directedCycleFamily r markers host ports root distinguished a y ∪
      directedCycleFamily r markers host ports root distinguished a z =
        cycleFamily r markers host ports := by
  classical
  ext edges
  simp only [mem_union, mem_directedCycleFamily]
  constructor
  · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
  · intro h
    have hc := ((mem_cycleFamily _ _ _ _ _).mp h).1
    exact (rootedDirectedCycle_exhaustive root distinguished a hpair hc).elim
      (fun hy => Or.inl ⟨h, hy⟩) (fun hz => Or.inr ⟨h, hz⟩)

/-- Distinct endpoint directions give disjoint classes. -/
theorem directedCycleFamily_disjoint {r : ℕ} {markers host : Finset (Finset V)}
    (hr : 3 ≤ r) (ports : Finset V) (root distinguished : ↥markers) (a : ↥root.val)
    {y z : V} (hyz : y ≠ z) :
    Disjoint (directedCycleFamily r markers host ports root distinguished a y)
      (directedCycleFamily r markers host ports root distinguished a z) := by
  classical
  apply disjoint_left.mpr
  intro edges hy hz
  exact hyz (rootedDirectedCycle_unique hr root distinguished a
    ((mem_directedCycleFamily _ _ _ _ _ _ _ _ _).mp hy).2
    ((mem_directedCycleFamily _ _ _ _ _ _ _ _ _).mp hz).2)

/-- Number of actual edge-set completions in one relative direction. -/
@[expose] def directedCycleCount (r : ℕ) (markers host : Finset (Finset V)) (ports : Finset V)
    (root distinguished : ↥markers) (a : ↥root.val) (y : V) : ℕ :=
  (directedCycleFamily r markers host ports root distinguished a y).card

/-- The directed-completion split holds for every host and fixed prohibition set. -/
theorem directedCycleCount_split {r : ℕ} {markers host : Finset (Finset V)}
    (hr : 3 ≤ r) (ports : Finset V) (root distinguished : ↥markers) (a : ↥root.val)
    {y z : V} (hpair : distinguished.val = {y, z}) (hyz : y ≠ z) :
    cycleCount r markers host ports =
      directedCycleCount r markers host ports root distinguished a y +
        directedCycleCount r markers host ports root distinguished a z := by
  classical
  change (cycleFamily r markers host ports).card = _
  rw [← directedCycleFamily_union ports root distinguished a hpair]
  exact card_union_of_disjoint (directedCycleFamily_disjoint hr ports root distinguished a hyz)

end LooseHamilton
