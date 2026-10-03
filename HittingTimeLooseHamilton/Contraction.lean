module

public import HittingTimeLooseHamilton.EnumerationBridge

public section

/-! The block labels obtained by contracting each prescribed marked edge. -/
noncomputable section
open Finset
namespace LooseHamilton
namespace MixedCycleWitness
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {r : ℕ} {markers edges : Finset (Finset V)}

abbrev ContractedBlock (C : MixedCycleWitness r markers edges) :=
  ↥markers ⊕ ↥C.ordinaryJunctionChoice.val

/-- Index of an ordinary junction in the unique cyclic presentation. -/
@[expose] def ordinaryJunctionIndex (C : MixedCycleWitness r markers edges)
    (v : ↥C.ordinaryJunctionChoice.val) : Fin C.length :=
  (mem_image.mp (mem_sdiff.mp v.property).1).choose

@[simp] theorem junction_ordinaryJunctionIndex (C : MixedCycleWitness r markers edges)
    (v : ↥C.ordinaryJunctionChoice.val) : C.junction (C.ordinaryJunctionIndex v) = v.val :=
  (mem_image.mp (mem_sdiff.mp v.property).1).choose_spec.2

/-- The ordinary slot leaving each contracted block. -/
@[expose] def outgoingSlot (C : MixedCycleWitness r markers edges) : C.ContractedBlock → Fin C.length
  | Sum.inl e => finRotate C.length (C.slot.symm (Sum.inl e))
  | Sum.inr v => C.ordinaryJunctionIndex v

lemma ordinary_junction_slot (C : MixedCycleWitness r markers edges)
    (v : ↥C.ordinaryJunctionChoice.val) :
    ∃ e : ↥edges, C.slot (C.ordinaryJunctionIndex v) = Sum.inr e := by
  cases hs : C.slot (C.ordinaryJunctionIndex v) with
  | inr e => exact ⟨e, rfl⟩
  | inl e =>
    have he := C.slot_edge (C.ordinaryJunctionIndex v)
    rw [hs] at he
    simp only at he
    have hv : v.val ∈ e.val := by rw [he]; simp
    have hp : v.val ∈ markers.biUnion id := mem_biUnion.mpr ⟨e.val, e.property, hv⟩
    exact False.elim ((mem_sdiff.mp v.property).2 hp)

lemma outgoingSlot_ordinary (C : MixedCycleWitness r markers edges) (b : C.ContractedBlock) :
    ∃ e : ↥edges, C.slot (C.outgoingSlot b) = Sum.inr e := by
  cases b with
  | inl e => exact C.ordinary_after_marker _ e (C.slot.apply_symm_apply _)
  | inr v => exact C.ordinary_junction_slot v

lemma outgoingSlot_marker_vertex (C : MixedCycleWitness r markers edges) (e : ↥markers) :
    C.junction (C.outgoingSlot (Sum.inl e)) ∈ markers.biUnion id := by
  have he := C.slot_edge (C.slot.symm (Sum.inl e))
  rw [C.slot.apply_symm_apply] at he
  simp only at he
  apply mem_biUnion.mpr
  refine ⟨e.val, e.property, ?_⟩
  rw [he]
  simp [outgoingSlot]

theorem outgoingSlot_injective (C : MixedCycleWitness r markers edges) :
    Function.Injective C.outgoingSlot := by
  intro a b hab
  cases a with
  | inl e =>
    cases b with
    | inl f =>
      have hs := (finRotate C.length).injective hab
      have ht := C.slot.symm.injective hs
      exact congrArg Sum.inl (Sum.inl.inj ht)
    | inr v =>
      have hp := C.outgoingSlot_marker_vertex e
      rw [hab] at hp
      have hv : C.junction (C.outgoingSlot (Sum.inr v)) = v.val := C.junction_ordinaryJunctionIndex v
      rw [hv] at hp
      exact False.elim ((mem_sdiff.mp v.property).2 hp)
  | inr v =>
    cases b with
    | inl e =>
      have hp := C.outgoingSlot_marker_vertex e
      rw [← hab] at hp
      have hv : C.junction (C.outgoingSlot (Sum.inr v)) = v.val := C.junction_ordinaryJunctionIndex v
      rw [hv] at hp
      exact False.elim ((mem_sdiff.mp v.property).2 hp)
    | inr w =>
      apply congrArg Sum.inr
      apply Subtype.ext
      have hh := congrArg C.junction hab
      simpa only [outgoingSlot, junction_ordinaryJunctionIndex] using hh

/-- Each contracted block has a unique outgoing ordinary edge. -/
@[expose] def outgoingEdge (C : MixedCycleWitness r markers edges) (b : C.ContractedBlock) : ↥edges :=
  (C.outgoingSlot_ordinary b).choose

@[simp] theorem slot_outgoingEdge (C : MixedCycleWitness r markers edges) (b : C.ContractedBlock) :
    C.slot (C.outgoingSlot b) = Sum.inr (C.outgoingEdge b) :=
  (C.outgoingSlot_ordinary b).choose_spec

theorem outgoingEdge_injective (C : MixedCycleWitness r markers edges) :
    Function.Injective C.outgoingEdge := by
  intro a b hab
  apply C.outgoingSlot_injective
  apply C.slot.injective
  rw [C.slot_outgoingEdge, C.slot_outgoingEdge, hab]

theorem contractedBlock_card (C : MixedCycleWitness r markers edges) :
    Fintype.card C.ContractedBlock = edges.card := by
  change Fintype.card (↥markers ⊕ ↥(univ.image C.junction \ originalPorts markers)) = _
  rw [Fintype.card_sum, Fintype.card_coe, Fintype.card_coe]
  unfold originalPorts
  rw [C.ordinary_junction_card]
  exact Nat.add_sub_of_le C.markers_card_le_edges_card

/-- Contracting the marked pairs identifies the k blocks with the k ordinary edges. -/
@[expose] def blockEdgeEquiv (C : MixedCycleWitness r markers edges) : C.ContractedBlock ≃ ↥edges :=
  Equiv.ofBijective C.outgoingEdge ⟨C.outgoingEdge_injective,
    (Fintype.bijective_iff_injective_and_card C.outgoingEdge).mpr
      ⟨C.outgoingEdge_injective, by rw [C.contractedBlock_card, Fintype.card_coe]⟩ |>.2⟩

end MixedCycleWitness
end LooseHamilton
