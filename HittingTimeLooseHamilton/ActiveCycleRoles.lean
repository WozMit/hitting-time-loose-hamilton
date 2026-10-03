module

public import HittingTimeLooseHamilton.EdgeRoles
public import HittingTimeLooseHamilton.CycleSurgery

public section

/-! # Intrinsic roles on an active vertex set

Endpoint and private-vertex sets are determined by actual mixed edges, even
when the cycle spans only an active subset of the ambient vertex type.
-/
noncomputable section
namespace LooseHamilton
namespace MixedCycleOnWitness
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {r : ℕ} {S : Finset V} {markers edges : Finset (Finset V)}

theorem marked_card (C : MixedCycleOnWitness r S markers edges)
    {e : Finset V} (he : e ∈ markers) : e.card = 2 := by
  have h := C.slot_edge (C.slot.symm (.inl ⟨e, he⟩))
  simp only [C.slot.apply_symm_apply] at h
  rw [h, card_pair (C.junction_next_ne _)]

theorem uniform (C : MixedCycleOnWitness r S markers edges) (hr : 3 ≤ r)
    {e : Finset V} (he : e ∈ edges) : e.card = r := by
  change (⟨e, he⟩ : ↥edges).val.card = r
  rw [C.edge_eq_endpointPair ⟨e, he⟩,
    card_union_of_disjoint (C.endpointPair_private_disjoint _),
    C.endpointPair_card, C.private_card]
  omega

@[expose] def slotSet (C : MixedCycleOnWitness r S markers edges) (i : Fin C.length) : Finset V :=
  Sum.elim Subtype.val Subtype.val (C.slot i)

theorem slotSet_mem (C : MixedCycleOnWitness r S markers edges) (i : Fin C.length) :
    C.slotSet i ∈ markers ∪ edges := by
  unfold slotSet
  cases C.slot i with
  | inl e => exact mem_union_left _ e.property
  | inr e => exact mem_union_right _ e.property

theorem slotSet_injective (C : MixedCycleOnWitness r S markers edges) (hr : 3 ≤ r) :
    Function.Injective C.slotSet := by
  intro i j hij
  apply C.slot.injective
  unfold slotSet at hij
  cases hi : C.slot i with
  | inl e =>
    cases hj : C.slot j with
    | inl f => simp only [hi, hj, Sum.elim_inl] at hij; exact congrArg Sum.inl (Subtype.ext hij)
    | inr f =>
      simp only [hi, hj, Sum.elim_inl, Sum.elim_inr] at hij
      have h1 := C.marked_card e.property
      have h2 := C.uniform hr f.property
      rw [hij] at h1
      omega
  | inr e =>
    cases hj : C.slot j with
    | inl f =>
      simp only [hi, hj, Sum.elim_inl, Sum.elim_inr] at hij
      have h1 := C.uniform hr e.property
      have h2 := C.marked_card f.property
      rw [hij] at h1
      omega
    | inr f => simp only [hi, hj, Sum.elim_inr] at hij; exact congrArg Sum.inr (Subtype.ext hij)

theorem slotSet_surjective (C : MixedCycleOnWitness r S markers edges)
    {e : Finset V} (he : e ∈ markers ∪ edges) : ∃ i, C.slotSet i = e := by
  rcases mem_union.mp he with hm | ho
  · exact ⟨C.slot.symm (.inl ⟨e, hm⟩), by simp [slotSet]⟩
  · exact ⟨C.slot.symm (.inr ⟨e, ho⟩), by simp [slotSet]⟩

theorem endpoint_mem_slotSet (C : MixedCycleOnWitness r S markers edges) (i : Fin C.length) :
    C.junction i ∈ C.slotSet i ∧ C.junction (finRotate C.length i) ∈ C.slotSet i := by
  have h := C.slot_edge i
  unfold slotSet
  cases hi : C.slot i with
  | inl e => rw [hi] at h; simp only at h; simp [h]
  | inr e => rw [hi] at h; simp only at h; simp [h]

/-- Private vertices are recovered by removing all junctions from their edge. -/
theorem private_eq_sdiff_junctions (C : MixedCycleOnWitness r S markers edges)
    (e : {e // e ∈ edges}) :
    C.privateBlock e = e.val \ univ.image C.junction := by
  have hs := C.slot_edge (C.slot.symm (Sum.inr e))
  rw [C.slot.apply_symm_apply] at hs
  simp only at hs
  ext v
  constructor
  · intro hv
    exact mem_sdiff.mpr ⟨(by rw [C.edge_eq_endpointPair e]; exact mem_union_right _ hv),
      fun hj => (disjoint_left.mp (C.junction_private_disjoint e)) hj hv⟩
  · intro hv
    obtain ⟨he, hn⟩ := mem_sdiff.mp hv
    rw [hs] at he
    rcases mem_union.mp he with he | hp
    · simp only [mem_insert, mem_singleton] at he
      rcases he with rfl | rfl <;> exact False.elim (hn (mem_image_of_mem _ (mem_univ _)))
    · exact hp

/-- A private vertex cannot belong to any edge other than its own. -/
theorem private_unique_edge (C : MixedCycleOnWitness r S markers edges)
    (e : {e // e ∈ edges}) {v : V} (hv : v ∈ C.privateBlock e)
    {f : Finset V} (hf : f ∈ markers ∪ edges) (hvf : v ∈ f) : f = e.val := by
  obtain ⟨i, rfl⟩ := C.slotSet_surjective hf
  have hn : v ∉ univ.image C.junction :=
    fun hj => disjoint_left.mp (C.junction_private_disjoint e) hj hv
  have hs := C.slot_edge i
  unfold slotSet at hvf ⊢
  cases hi : C.slot i with
  | inl f =>
    rw [hi] at hs
    simp only at hs
    simp only [hi, Sum.elim_inl] at hvf
    rw [hs] at hvf
    simp only [mem_insert, mem_singleton] at hvf
    rcases hvf with rfl | rfl <;> exact False.elim (hn (mem_image_of_mem _ (mem_univ _)))
  | inr f =>
    rw [hi] at hs
    simp only at hs
    simp only [hi, Sum.elim_inr] at hvf ⊢
    rw [hs] at hvf
    rcases mem_union.mp hvf with hj | hp
    · simp only [mem_insert, mem_singleton] at hj
      rcases hj with rfl | rfl <;> exact False.elim (hn (mem_image_of_mem _ (mem_univ _)))
    · by_contra hne
      have hef : e ≠ f := fun h => hne (congrArg Subtype.val h.symm)
      exact disjoint_left.mp (C.private_disjoint hef) hv hp

/-- Junctions are exactly the vertices incident with two different mixed edges. -/
theorem mem_junctions_iff (C : MixedCycleOnWitness r S markers edges) (hr : 3 ≤ r) (v : V) :
    v ∈ univ.image C.junction ↔
      ∃ e ∈ markers ∪ edges, ∃ f ∈ markers ∪ edges, e ≠ f ∧ v ∈ e ∧ v ∈ f := by
  constructor
  · intro hv
    obtain ⟨i, _, rfl⟩ := mem_image.mp hv
    let j := (finRotate C.length).symm i
    have hji : finRotate C.length j = i := (finRotate C.length).apply_symm_apply i
    refine ⟨C.slotSet i, C.slotSet_mem i, C.slotSet j, C.slotSet_mem j, ?_,
      (C.endpoint_mem_slotSet i).1, ?_⟩
    · intro he
      have hij := C.slotSet_injective hr he
      have hn := C.junction_next_ne j
      rw [hji, ← hij] at hn
      exact hn rfl
    · simpa only [hji] using (C.endpoint_mem_slotSet j).2
  · rintro ⟨e, he, f, hf, hef, hve, hvf⟩
    by_contra hn
    have hc : v ∈ univ.image C.junction ∪ univ.biUnion C.privateBlock := by
      rw [← C.cover]
      rcases mem_union.mp he with he | he
      · exact C.marked_subset_active he hve
      · exact C.edge_subset_active he hve
    have hp := (mem_union.mp hc).resolve_left hn
    obtain ⟨a, _, ha⟩ := mem_biUnion.mp hp
    exact hef ((C.private_unique_edge a ha he hve).trans (C.private_unique_edge a ha hf hvf).symm)

/-- Any two presentations of one cycle have the same junctions. -/
theorem junctions_eq (C D : MixedCycleOnWitness r S markers edges) (hr : 3 ≤ r) :
    univ.image C.junction = univ.image D.junction := by
  ext v
  rw [C.mem_junctions_iff hr, D.mem_junctions_iff hr]

/-- All private blocks are independent of the presentation. -/
theorem privateBlock_eq (C D : MixedCycleOnWitness r S markers edges) (hr : 3 ≤ r)
    (e : {e // e ∈ edges}) : C.privateBlock e = D.privateBlock e := by
  rw [C.private_eq_sdiff_junctions, D.private_eq_sdiff_junctions, C.junctions_eq D hr]

/-- Intersecting a slot edge with the intrinsic junction set recovers its two endpoints. -/
theorem slotSet_inter_junctions (C : MixedCycleOnWitness r S markers edges) (i : Fin C.length) :
    C.slotSet i ∩ univ.image C.junction =
      {C.junction i, C.junction (finRotate C.length i)} := by
  have hs := C.slot_edge i
  unfold slotSet
  cases hi : C.slot i with
  | inl e =>
    rw [hi] at hs
    simp only at hs
    simp only [Sum.elim_inl]
    rw [hs]
    apply inter_eq_left.mpr
    intro v hv
    simp only [mem_insert, mem_singleton] at hv
    rcases hv with rfl | rfl <;> exact mem_image_of_mem _ (mem_univ _)
  | inr e =>
    rw [hi] at hs
    simp only at hs
    simp only [Sum.elim_inr]
    rw [hs, union_inter_distrib_right]
    have hp : C.privateBlock e ∩ univ.image C.junction = ∅ :=
      disjoint_iff_inter_eq_empty.mp (C.junction_private_disjoint e).symm
    rw [hp, union_empty]
    apply inter_eq_left.mpr
    intro v hv
    simp only [mem_insert, mem_singleton] at hv
    rcases hv with rfl | rfl <;> exact mem_image_of_mem _ (mem_univ _)

theorem cycleJunctions_eq (C : MixedCycleOnWitness r S markers edges) (hr : 3 ≤ r) :
    cycleJunctions markers edges = univ.image C.junction := by
  ext v
  simp only [cycleJunctions, mem_filter, mem_univ, true_and]
  exact (C.mem_junctions_iff hr v).symm

theorem edgeEndpointPair_eq (C : MixedCycleOnWitness r S markers edges) (hr : 3 ≤ r)
    (e : ↥edges) : edgeEndpointPair markers edges e.val = C.endpointPair e := by
  rw [edgeEndpointPair, C.cycleJunctions_eq hr]
  simpa only [slotSet, C.slot.apply_symm_apply, Sum.elim_inr, endpointPair] using
    C.slotSet_inter_junctions (C.slot.symm (.inr e))

theorem private_eq_sdiff_endpointPair (C : MixedCycleOnWitness r S markers edges)
    (hr : 3 ≤ r) (e : ↥edges) :
    C.privateBlock e = e.val \ edgeEndpointPair markers edges e.val := by
  rw [edgeEndpointPair, sdiff_inter_self_left, C.cycleJunctions_eq hr]
  exact C.private_eq_sdiff_junctions e

end MixedCycleOnWitness
end LooseHamilton
