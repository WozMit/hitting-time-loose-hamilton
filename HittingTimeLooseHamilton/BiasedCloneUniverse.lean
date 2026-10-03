module

public import HittingTimeLooseHamilton.BiasedCloneMatching

public section

/-! The active clone slots depend only on junctions and marker orientations. -/
noncomputable section
open Finset
namespace LooseHamilton.MixedCycleWitness
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {r : ℕ} {markers edges : Finset (Finset V)}

@[expose] def markerStarts (C : MixedCycleWitness r markers edges) : Finset V :=
  univ.image (fun e : ↥markers => C.junction (C.slot.symm (.inl e)))
@[expose] def markerEnds (C : MixedCycleWitness r markers edges) : Finset V :=
  univ.image (fun e : ↥markers => C.junction (finRotate C.length (C.slot.symm (.inl e))))

theorem exists_ordinary_start (C : MixedCycleWitness r markers edges) (v : V) :
    (∃ e : ↥edges, v = C.junction (C.slot.symm (.inr e))) ↔
      v ∈ univ.image C.junction ∧ v ∉ C.markerStarts := by
  constructor
  · rintro ⟨e, rfl⟩
    refine ⟨mem_image_of_mem _ (mem_univ _), ?_⟩
    intro h
    obtain ⟨m, _, hm⟩ := mem_image.mp h
    have he := C.slot.symm.injective (C.junction_injective hm)
    cases he
  · rintro ⟨hv, hn⟩
    obtain ⟨i, _, rfl⟩ := mem_image.mp hv
    cases hs : C.slot i with
    | inl m =>
      exfalso
      apply hn
      exact mem_image.mpr ⟨m, mem_univ _, congrArg C.junction (by rw [← hs]; simp)⟩
    | inr e => exact ⟨e, congrArg C.junction (by rw [← hs]; simp)⟩

theorem exists_ordinary_end (C : MixedCycleWitness r markers edges) (v : V) :
    (∃ e : ↥edges, v = C.junction (finRotate C.length (C.slot.symm (.inr e)))) ↔
      v ∈ univ.image C.junction ∧ v ∉ C.markerEnds := by
  constructor
  · rintro ⟨e, rfl⟩
    refine ⟨mem_image_of_mem _ (mem_univ _), ?_⟩
    intro h
    obtain ⟨m, _, hm⟩ := mem_image.mp h
    have he := C.slot.symm.injective ((finRotate C.length).injective (C.junction_injective hm))
    cases he
  · rintro ⟨hv, hn⟩
    obtain ⟨i, _, rfl⟩ := mem_image.mp hv
    let j := (finRotate C.length).symm i
    have hj : finRotate C.length j = i := (finRotate C.length).apply_symm_apply i
    cases hs : C.slot j with
    | inl m =>
      exfalso
      apply hn
      exact mem_image.mpr ⟨m, mem_univ _, congrArg C.junction (by rw [← hs]; simpa using hj)⟩
    | inr e =>
      refine ⟨e, congrArg C.junction ?_⟩
      rw [← hs, C.slot.symm_apply_apply, hj]

theorem exists_private_vertex (C : MixedCycleWitness r markers edges) (v : V) :
    (∃ e : ↥edges, v ∈ C.privateBlock e) ↔ v ∉ univ.image C.junction := by
  constructor
  · rintro ⟨e, he⟩ hv
    exact disjoint_left.mp (C.junction_private_disjoint e) hv he
  · intro hn
    have hv : v ∈ univ.image C.junction ∪ univ.biUnion C.privateBlock := by
      rw [← C.cover]
      exact mem_univ _
    obtain ⟨e, _, he⟩ := mem_biUnion.mp ((mem_union.mp hv).resolve_left hn)
    exact ⟨e, he⟩

theorem mem_cloneVertices (C : MixedCycleWitness r markers edges) (v : V) (t : Fin 3) :
    (v,t) ∈ C.cloneVertices ↔
      (v ∈ univ.image C.junction ∧ v ∉ C.markerStarts ∧ t = 0) ∨
      (v ∈ univ.image C.junction ∧ v ∉ C.markerEnds ∧ t = 1) ∨
      (v ∉ univ.image C.junction ∧ t = 2) := by
  simp only [cloneVertices, mem_biUnion, mem_univ, true_and, mem_cloneEdge,
    exists_or, exists_and_right, exists_ordinary_start, exists_ordinary_end,
    exists_private_vertex, and_assoc]

/-- No edge-set information beyond junctions and marker directions is needed
for the common clone vertex universe in a conditional role fibre. -/
theorem cloneVertices_eq_of_roles {edges' : Finset (Finset V)}
    (C : MixedCycleWitness r markers edges) (D : MixedCycleWitness r markers edges')
    (hJ : univ.image C.junction = univ.image D.junction)
    (hs : C.markerStarts = D.markerStarts) (he : C.markerEnds = D.markerEnds) :
    C.cloneVertices = D.cloneVertices := by
  ext ⟨v,t⟩
  simp only [mem_cloneVertices, hJ, hs, he]

/-- On a fixed marked pair the starting endpoint determines the ending endpoint. -/
theorem marker_end_eq_of_start {edges' : Finset (Finset V)}
    (C : MixedCycleWitness r markers edges) (D : MixedCycleWitness r markers edges')
    (e : ↥markers)
    (hs : C.junction (C.slot.symm (.inl e)) = D.junction (D.slot.symm (.inl e))) :
    C.junction (finRotate C.length (C.slot.symm (.inl e))) =
      D.junction (finRotate D.length (D.slot.symm (.inl e))) := by
  have hc := C.slot_edge (C.slot.symm (.inl e))
  have hd := D.slot_edge (D.slot.symm (.inl e))
  rw [C.slot.apply_symm_apply] at hc
  rw [D.slot.apply_symm_apply] at hd
  simp only at hc hd
  have hm : C.junction (finRotate C.length (C.slot.symm (.inl e))) ∈ e.val := by
    rw [hc]
    simp
  rw [hd] at hm
  rcases mem_insert.mp hm with hm | hm
  · exact False.elim (C.junction_next_ne _ (hs.trans hm.symm))
  · exact mem_singleton.mp hm

theorem cloneVertices_eq_of_junction_marker_starts {edges' : Finset (Finset V)}
    (C : MixedCycleWitness r markers edges) (D : MixedCycleWitness r markers edges')
    (hJ : univ.image C.junction = univ.image D.junction)
    (hs : ∀ e : ↥markers, C.markerStart e = D.markerStart e) :
    C.cloneVertices = D.cloneVertices := by
  have hs' : ∀ e : ↥markers, C.junction (C.slot.symm (.inl e)) =
      D.junction (D.slot.symm (.inl e)) := fun e => congrArg Subtype.val (hs e)
  apply C.cloneVertices_eq_of_roles D hJ
  · unfold markerStarts
    congr 1
    funext e
    exact hs' e
  · unfold markerEnds
    congr 1
    funext e
    exact C.marker_end_eq_of_start D e (hs' e)

end LooseHamilton.MixedCycleWitness
