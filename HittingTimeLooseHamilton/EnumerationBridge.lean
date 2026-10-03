module

public import HittingTimeLooseHamilton.Counting
public import HittingTimeLooseHamilton.JunctionChoices

public section

/-! Reconstruction of the intrinsic junction and private-vertex sets. -/
noncomputable section
open Finset
namespace LooseHamilton
namespace MixedCycleWitness
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {r : ℕ} {markers edges : Finset (Finset V)}

@[expose] def slotSet (C : MixedCycleWitness r markers edges) (i : Fin C.length) : Finset V :=
  Sum.elim Subtype.val Subtype.val (C.slot i)

theorem slotSet_mem (C : MixedCycleWitness r markers edges) (i : Fin C.length) :
    C.slotSet i ∈ markers ∪ edges := by
  unfold slotSet
  cases C.slot i with
  | inl e => exact mem_union_left _ e.property
  | inr e => exact mem_union_right _ e.property

theorem slotSet_injective (C : MixedCycleWitness r markers edges) (hr : 3 ≤ r) :
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

theorem slotSet_surjective (C : MixedCycleWitness r markers edges)
    {e : Finset V} (he : e ∈ markers ∪ edges) : ∃ i, C.slotSet i = e := by
  rcases mem_union.mp he with hm | ho
  · exact ⟨C.slot.symm (.inl ⟨e, hm⟩), by simp [slotSet]⟩
  · exact ⟨C.slot.symm (.inr ⟨e, ho⟩), by simp [slotSet]⟩

theorem endpoint_mem_slotSet (C : MixedCycleWitness r markers edges) (i : Fin C.length) :
    C.junction i ∈ C.slotSet i ∧ C.junction (finRotate C.length i) ∈ C.slotSet i := by
  have h := C.slot_edge i
  unfold slotSet
  cases hi : C.slot i with
  | inl e => rw [hi] at h; simp only at h; simp [h]
  | inr e => rw [hi] at h; simp only at h; simp [h]

/-- Private vertices are recovered by removing all junctions from their edge. -/
theorem private_eq_sdiff_junctions (C : MixedCycleWitness r markers edges)
    (e : {e // e ∈ edges}) :
    C.privateBlock e = e.val \ univ.image C.junction := by
  have hs := C.slot_edge (C.slot.symm (Sum.inr e))
  rw [C.slot.apply_symm_apply] at hs
  simp only at hs
  ext v
  constructor
  · intro hv
    exact mem_sdiff.mpr ⟨C.private_subset e hv,
      fun hj => (disjoint_left.mp (C.junction_private_disjoint e)) hj hv⟩
  · intro hv
    obtain ⟨he, hn⟩ := mem_sdiff.mp hv
    rw [hs] at he
    rcases mem_union.mp he with he | hp
    · simp only [mem_insert, mem_singleton] at he
      rcases he with rfl | rfl <;> exact False.elim (hn (mem_image_of_mem _ (mem_univ _)))
    · exact hp

/-- A private vertex cannot belong to any edge other than its own. -/
theorem private_unique_edge (C : MixedCycleWitness r markers edges)
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
theorem mem_junctions_iff (C : MixedCycleWitness r markers edges) (hr : 3 ≤ r) (v : V) :
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
      rw [← C.cover]; exact mem_univ _
    have hp := (mem_union.mp hc).resolve_left hn
    obtain ⟨a, _, ha⟩ := mem_biUnion.mp hp
    exact hef ((C.private_unique_edge a ha he hve).trans (C.private_unique_edge a ha hf hvf).symm)

/-- Any two presentations of one cycle have the same junctions. -/
theorem junctions_eq (C D : MixedCycleWitness r markers edges) (hr : 3 ≤ r) :
    univ.image C.junction = univ.image D.junction := by
  ext v
  rw [C.mem_junctions_iff hr, D.mem_junctions_iff hr]

/-- All private blocks are independent of the presentation. -/
theorem privateBlock_eq (C D : MixedCycleWitness r markers edges) (hr : 3 ≤ r)
    (e : {e // e ∈ edges}) : C.privateBlock e = D.privateBlock e := by
  rw [C.private_eq_sdiff_junctions, D.private_eq_sdiff_junctions, C.junctions_eq D hr]

/-- Intersecting a slot edge with the intrinsic junction set recovers its two endpoints. -/
theorem slotSet_inter_junctions (C : MixedCycleWitness r markers edges) (i : Fin C.length) :
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

/-- The two endpoint sets of all mixed edges are intrinsic. -/
theorem endpoints_eq_of_slotSet_eq (C D : MixedCycleWitness r markers edges) (hr : 3 ≤ r)
    (i : Fin C.length) (j : Fin D.length) (he : C.slotSet i = D.slotSet j) :
    {C.junction i, C.junction (finRotate C.length i)} =
      ({D.junction j, D.junction (finRotate D.length j)} : Finset V) := by
  rw [← C.slotSet_inter_junctions, ← D.slotSet_inter_junctions,
    he, C.junctions_eq D hr]

/-- Every junction in an edge is one of its two endpoints. -/
theorem junction_mem_slotSet_iff (C : MixedCycleWitness r markers edges)
    (i j : Fin C.length) :
    C.junction i ∈ C.slotSet j ↔ i = j ∨ i = finRotate C.length j := by
  have hmem : C.junction i ∈ univ.image C.junction := mem_image_of_mem _ (mem_univ _)
  have hx := C.slotSet_inter_junctions j
  have hh := congrArg (fun S => C.junction i ∈ S) hx
  simpa only [mem_inter, hmem, and_true, mem_insert, mem_singleton,
    C.junction_injective.eq_iff] using (iff_of_eq hh)

/-- A fixed directed edge forces the direction of the next junction. -/
theorem next_junction_eq (C D : MixedCycleWitness r markers edges) (hr : 3 ≤ r)
    (i : Fin C.length) (j : Fin D.length)
    (he : C.slotSet i = D.slotSet j) (hv : C.junction i = D.junction j) :
    C.junction (finRotate C.length i) = D.junction (finRotate D.length j) := by
  have hp := C.endpoints_eq_of_slotSet_eq D hr i j he
  have hm : C.junction (finRotate C.length i) ∈
      ({D.junction j, D.junction (finRotate D.length j)} : Finset V) := by
    rw [← hp]; simp
  simp only [mem_insert, mem_singleton] at hm
  rcases hm with hm | hm
  · exact False.elim (C.junction_next_ne i (hv.trans hm.symm))
  · exact hm

/-- Once an edge and its direction are fixed, the next edge is forced. -/
theorem next_slotSet_eq (C D : MixedCycleWitness r markers edges) (hr : 3 ≤ r)
    (i : Fin C.length) (j : Fin D.length)
    (he : C.slotSet i = D.slotSet j) (hv : C.junction i = D.junction j) :
    C.slotSet (finRotate C.length i) = D.slotSet (finRotate D.length j) := by
  have hn := C.next_junction_eq D hr i j he hv
  obtain ⟨t, ht⟩ := C.slotSet_surjective (D.slotSet_mem (finRotate D.length j))
  have hm : C.junction (finRotate C.length i) ∈ C.slotSet t := by
    rw [ht, hn]
    exact (D.endpoint_mem_slotSet (finRotate D.length j)).1
  rcases (C.junction_mem_slotSet_iff _ _).mp hm with h | h
  · rw [← h] at ht
    exact ht
  · have hit : i = t := (finRotate C.length).injective h
    have hneq : j ≠ finRotate D.length j := fun h => D.junction_next_ne j (congrArg D.junction h)
    have hfalse : D.slotSet j = D.slotSet (finRotate D.length j) := by
      rw [← he, hit, ht]
    exact False.elim (hneq (D.slotSet_injective hr hfalse))

/-- Rooting and orienting a mixed edge determines the entire presentation by
walking around it. This is the uniqueness needed to avoid overcounting cycles. -/
theorem iterate_eq (C D : MixedCycleWitness r markers edges) (hr : 3 ≤ r)
    (i : Fin C.length) (j : Fin D.length)
    (he : C.slotSet i = D.slotSet j) (hv : C.junction i = D.junction j) (n : ℕ) :
    C.slotSet ((finRotate C.length)^[n] i) = D.slotSet ((finRotate D.length)^[n] j) ∧
    C.junction ((finRotate C.length)^[n] i) = D.junction ((finRotate D.length)^[n] j) := by
  induction n with
  | zero => exact ⟨he, hv⟩
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    exact ⟨C.next_slotSet_eq D hr _ _ ih.1 ih.2,
      C.next_junction_eq D hr _ _ ih.1 ih.2⟩

/-- The ordinary junction choice extracted from a cyclic presentation. -/
@[expose] def ordinaryJunctionChoice (C : MixedCycleWitness r markers edges) :
    ↥(ordinaryJunctionChoices markers edges.card) :=
  ⟨univ.image C.junction \ markers.biUnion id, by
    rw [mem_ordinaryJunctionChoices]
    refine ⟨?_, C.ordinary_junction_card⟩
    intro v hv
    exact mem_sdiff.mpr ⟨mem_univ _, (mem_sdiff.mp hv).2⟩⟩

/-- The start endpoint of any marker in a directed cyclic presentation. -/
@[expose] def markerStart (C : MixedCycleWitness r markers edges) (e : ↥markers) : ↥e.val := by
  let i := C.slot.symm (Sum.inl e)
  refine ⟨C.junction i, ?_⟩
  have hs := C.slot_edge i
  rw [C.slot.apply_symm_apply] at hs
  simp only at hs
  rw [hs]
  simp

/-- All non-root marker directions extracted from a directed presentation. -/
@[expose] def markerDirections (C : MixedCycleWitness r markers edges) (root : Finset V) :
    MarkerDirections markers root := fun e =>
  C.markerStart ⟨e.val, mem_of_mem_erase e.property⟩

/-- The ordinary junction choice is independent of the chosen presentation. -/
theorem ordinaryJunctionChoice_eq (C D : MixedCycleWitness r markers edges) (hr : 3 ≤ r) :
    C.ordinaryJunctionChoice = D.ordinaryJunctionChoice := by
  apply Subtype.ext
  dsimp [ordinaryJunctionChoice]
  rw [C.junctions_eq D hr]

/-- Marked slots cannot be consecutive because the prescribed pairs are disjoint. -/
theorem markers_not_consecutive (C : MixedCycleWitness r markers edges)
    (i : Fin C.length) (e f : ↥markers)
    (he : C.slot i = Sum.inl e)
    (hf : C.slot (finRotate C.length i) = Sum.inl f) : False := by
  have hne : e.val ≠ f.val := by
    intro h
    have hs : e = f := Subtype.ext h
    have hi : i = finRotate C.length i := C.slot.injective (by rw [he, hf, hs])
    exact C.junction_next_ne i (congrArg C.junction hi)
  have hd : Disjoint e.val f.val := C.marked_matching e.property f.property hne
  have hleft := C.slot_edge i
  have hright := C.slot_edge (finRotate C.length i)
  rw [he] at hleft
  rw [hf] at hright
  simp only at hleft hright
  have hv1 : C.junction (finRotate C.length i) ∈ e.val := by rw [hleft]; simp
  have hv2 : C.junction (finRotate C.length i) ∈ f.val := by rw [hright]; simp
  exact disjoint_left.mp hd hv1 hv2

/-- An ordinary slot follows each marked slot. -/
theorem ordinary_after_marker (C : MixedCycleWitness r markers edges)
    (i : Fin C.length) (e : ↥markers) (he : C.slot i = Sum.inl e) :
    ∃ f : ↥edges, C.slot (finRotate C.length i) = Sum.inr f := by
  cases hf : C.slot (finRotate C.length i) with
  | inl f => exact False.elim (C.markers_not_consecutive i e f he hf)
  | inr f => exact ⟨f, rfl⟩

end MixedCycleWitness
end LooseHamilton
