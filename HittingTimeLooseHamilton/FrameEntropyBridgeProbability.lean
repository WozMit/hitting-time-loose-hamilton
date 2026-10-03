module

public import HittingTimeLooseHamilton.FrameEntropyBridgeRooted

public section

noncomputable section
namespace LooseHamilton.AuxiliaryFrame.Frame
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {r : ℕ} {original : Finset (Finset V)}

lemma numberedWitness_root (F : Frame r original)
    {E : Finset (Finset V)} (C : MixedCycleOnWitness r F.active F.markers E)
    (hC : F.Directed C) :
    (C.restrict.relabelVia F.vertexNumbering).markerStart F.numberedRoot = F.numberedInitial := by
  apply Subtype.ext
  change ((C.restrict.relabelVia F.vertexNumbering).markerStart
    (vertexEdgeEquiv F.vertexNumbering (restrictEdges F.active F.markers)
      (activeRestrictedMarker F.active F.rootMarker))).val = F.vertexNumbering _
  rw [MixedCycleWitness.relabelVia_markerStart]
  apply F.vertexNumbering.injective.eq_iff.mpr
  apply Subtype.ext
  rw [MixedCycleOnWitness.restrict_markerStart_val]
  obtain ⟨m,hm,hs⟩ := hC.1
  have he : m = F.rootMarker := Subtype.ext hm
  simpa only [he] using hs

private lemma restricted_inverse_edge (F : Frame r original)
    {E : Finset (Finset V)} (C : MixedCycleOnWitness r F.active F.markers E) (e : ↥E) :
    C.restrict.slot.symm (.inr (restrictedEdgeEquiv F.active E
      (fun _ h => C.edge_subset_active h) e)) = C.slot.symm (.inr e) := by
  apply C.restrict.slot.injective
  rw [Equiv.apply_symm_apply]
  change _ = (Equiv.sumCongr
    (restrictedEdgeEquiv F.active F.markers (fun _ h => C.marked_subset_active h))
    (restrictedEdgeEquiv F.active E (fun _ h => C.edge_subset_active h)))
    (C.slot (C.slot.symm (.inr e)))
  rw [Equiv.apply_symm_apply]
  rfl

lemma numberedWitness_start (F : Frame r original)
    {E : Finset (Finset V)} (C : MixedCycleOnWitness r F.active F.markers E)
    (e : ↥E) :
    let A := C.restrict.relabelVia F.vertexNumbering
    A.junction (A.slot.symm (.inr
      (vertexEdgeEquiv F.vertexNumbering (restrictEdges F.active E)
        (restrictedEdgeEquiv F.active E (fun _ h => C.edge_subset_active h) e)))) =
      F.vertexNumbering ⟨C.junction (C.slot.symm (.inr e)), C.junction_mem _⟩ := by
  dsimp only
  rw [MixedCycleWitness.relabelVia_slot_start]
  congr 1
  apply Subtype.ext
  change C.junction (C.restrict.slot.symm (.inr (restrictedEdgeEquiv F.active E
    (fun _ h => C.edge_subset_active h) e))) = _
  rw [restricted_inverse_edge]

lemma numberedWitness_end (F : Frame r original)
    {E : Finset (Finset V)} (C : MixedCycleOnWitness r F.active F.markers E)
    (e : ↥E) :
    let A := C.restrict.relabelVia F.vertexNumbering
    A.junction (finRotate A.length (A.slot.symm (.inr
      (vertexEdgeEquiv F.vertexNumbering (restrictEdges F.active E)
        (restrictedEdgeEquiv F.active E (fun _ h => C.edge_subset_active h) e))))) =
      F.vertexNumbering ⟨C.junction (finRotate C.length (C.slot.symm (.inr e))), C.junction_mem _⟩ := by
  dsimp only
  rw [MixedCycleWitness.relabelVia_slot_end]
  congr 1
  apply Subtype.ext
  change C.junction (finRotate C.length (C.restrict.slot.symm (.inr (restrictedEdgeEquiv F.active E
    (fun _ h => C.edge_subset_active h) e)))) = _
  rw [restricted_inverse_edge]

/-- Rooted roles in the numbered spanning cycle are exactly the genuine frame roles. -/
theorem numberedCycle_role_iff (F : Frame r original) (hr : 3 ≤ r)
    (H : Finset (Finset V)) (E : ↥(F.cycleFamily H))
    {c : Finset V × V × V} (hc : F.LegalCandidate c)
    (u v : ↥F.active) (hu : u.val = c.2.1) (hv : v.val = c.2.2) :
    rootedOrdinaryRole r (F.numberedEdges F.markers) (F.numberedCycle H E).val
      F.numberedRoot F.numberedInitial (F.numberedEdge (c.1 ∪ {c.2.1,c.2.2}))
      (F.vertexNumbering u) (F.vertexNumbering v) ↔ F.Role E.val c := by
  obtain ⟨hE,C,hC⟩ := (F.mem_cycleFamily H E.val).mp E.property
  let A := C.restrict.relabelVia F.vertexNumbering
  change rootedOrdinaryRole r (vertexEdges F.vertexNumbering (restrictEdges F.active F.markers))
    (vertexEdges F.vertexNumbering (restrictEdges F.active E.val)) _ _ _ _ _ ↔ _
  rw [rootedOrdinaryRole_iff_in_witness hr A _ _ (F.numberedWitness_root C hC),
    F.role_iff_in_witness hr hc C hC]
  have hsub : ∀ e ∈ E.val, e ⊆ F.active := fun e he => (mem_filter.mp (hE he)).2
  have hstart (he : c.1 ∪ {c.2.1,c.2.2} ∈ E.val)
      (he' : F.numberedEdge (c.1 ∪ {c.2.1,c.2.2}) ∈ F.numberedEdges E.val) :
      A.junction (A.slot.symm (.inr ⟨_,he'⟩)) =
        F.vertexNumbering ⟨C.junction (C.slot.symm (.inr ⟨_,he⟩)),C.junction_mem _⟩ :=
    F.numberedWitness_start C ⟨_,he⟩
  have hend (he : c.1 ∪ {c.2.1,c.2.2} ∈ E.val)
      (he' : F.numberedEdge (c.1 ∪ {c.2.1,c.2.2}) ∈ F.numberedEdges E.val) :
      A.junction (finRotate A.length (A.slot.symm (.inr ⟨_,he'⟩))) =
        F.vertexNumbering ⟨C.junction (finRotate C.length (C.slot.symm (.inr ⟨_,he⟩))),C.junction_mem _⟩ :=
    F.numberedWitness_end C ⟨_,he⟩
  constructor
  · rintro ⟨he,hs,ht⟩
    have he' := (F.mem_numberedEdges_iff hsub hc.2.1).mp he
    rw [hstart he' he] at hs
    rw [hend he' he] at ht
    exact ⟨he',(congrArg Subtype.val (F.vertexNumbering.injective hs)).trans hu,
      (congrArg Subtype.val (F.vertexNumbering.injective ht)).trans hv⟩
  · rintro ⟨he,hs,ht⟩
    have he' := (F.mem_numberedEdges_iff hsub hc.2.1).mpr he
    refine ⟨he',?_,?_⟩
    · rw [hstart he he']
      exact congrArg F.vertexNumbering (Subtype.ext (hs.trans hu.symm))
    · rw [hend he he']
      exact congrArg F.vertexNumbering (Subtype.ext (ht.trans hv.symm))

/-- The entropy model's actual role probability is the exact completion ratio. -/
theorem numberedCycleLaw_role (F : Frame r original) (hr : 3 ≤ r)
    (H : Finset (Finset V)) (hX : (F.cycleFamily H).Nonempty)
    {c : Finset V × V × V} (hc : F.LegalCandidate c)
    (hedge : c.1 ∪ {c.2.1,c.2.2} ∈ F.rawHost H)
    (u v : ↥F.active) (hu : u.val = c.2.1) (hv : v.val = c.2.2) :
    directedRoleProbability r (F.numberedEdges F.markers) (F.numberedEdges (F.rawHost H))
      F.numberedRoot F.numberedInitial (F.numberedCycleLaw H hX)
      (F.numberedEdge (c.1 ∪ {c.2.1,c.2.2})) (F.vertexNumbering u) (F.vertexNumbering v) =
      (F.completionCount H c : ℝ) / F.cycleCount H := by
  rw [← F.cycleLaw_role hr H hX hc hedge]
  unfold directedRoleProbability
  rw [F.numberedCycleLaw_event]
  letI : Nonempty ↥(F.cycleFamily H) := hX.to_subtype
  change _ = (FiniteEntropy.uniform.map (Subtype.val : ↥(F.cycleFamily H) → _)).event _
  rw [FiniteEntropy.Law.event_map]
  congr 1
  funext E
  exact propext (F.numberedCycle_role_iff hr H E hc u v hu hv)

end LooseHamilton.AuxiliaryFrame.Frame
