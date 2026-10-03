module

public import HittingTimeLooseHamilton.JunctionChoices

public section

/-! # Orienting prescribed marker pairs
A fixed first endpoint of the root removes the reversal ambiguity. The remaining
marker directions are exactly the two choices counted by `MarkerDirections`.
-/
noncomputable section
namespace LooseHamilton
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The unique endpoint of a pair other than the selected first endpoint. -/
@[expose] def otherEndpoint (e : Finset V) (he : e.card = 2) (a : ↥e) : ↥e := by
  have hn : (e.erase a.val).Nonempty := by
    rw [← card_pos, card_erase_of_mem a.property, he]
    decide
  let b := Classical.choose hn
  have hb := Classical.choose_spec hn
  exact ⟨b, mem_of_mem_erase hb⟩

theorem otherEndpoint_ne (e : Finset V) (he : e.card = 2) (a : ↥e) :
    (otherEndpoint e he a).val ≠ a.val := by
  exact (mem_erase.mp (Classical.choose_spec
    (show (e.erase a.val).Nonempty by
      rw [← card_pos, card_erase_of_mem a.property, he]; decide))).1

theorem pair_eq_endpoints (e : Finset V) (he : e.card = 2) (a : ↥e) :
    e = {a.val, (otherEndpoint e he a).val} := by
  apply (eq_of_subset_of_card_le ?_ ?_).symm
  · intro v hv
    simp only [mem_insert, mem_singleton] at hv
    rcases hv with rfl | rfl
    · exact a.property
    · exact (otherEndpoint e he a).property
  · simp [he, (otherEndpoint_ne e he a).symm]

/-- A deterministic first endpoint for the root pair (its particular choice is
irrelevant to the count). -/
@[expose] def rootEndpoint {markers : Finset (Finset V)} (hM : IsPairMatching markers)
    (root : Finset V) (hroot : root ∈ markers) : ↥root := by
  have hn : root.Nonempty := by rw [← card_pos, hM.1 root hroot]; decide
  exact ⟨Classical.choose hn, Classical.choose_spec hn⟩

@[expose] def markerFirst {markers : Finset (Finset V)} (hM : IsPairMatching markers)
    (root : Finset V) (hroot : root ∈ markers) (directions : MarkerDirections markers root)
    (e : ↥markers) : ↥e.val := by
  by_cases he : e.val = root
  · exact ⟨(rootEndpoint hM root hroot).val, by rw [he]; exact (rootEndpoint hM root hroot).property⟩
  · exact directions ⟨e.val, mem_erase.mpr ⟨he, e.property⟩⟩

@[expose] def markerLast {markers : Finset (Finset V)} (hM : IsPairMatching markers)
    (root : Finset V) (hroot : root ∈ markers) (directions : MarkerDirections markers root)
    (e : ↥markers) : ↥e.val :=
  otherEndpoint e.val (hM.1 e.val e.property) (markerFirst hM root hroot directions e)

theorem markerLast_ne_first {markers : Finset (Finset V)} (hM : IsPairMatching markers)
    (root : Finset V) (hroot : root ∈ markers) (directions : MarkerDirections markers root)
    (e : ↥markers) :
    (markerLast hM root hroot directions e).val ≠ (markerFirst hM root hroot directions e).val :=
  otherEndpoint_ne _ _ _

theorem marker_eq_endpoints {markers : Finset (Finset V)} (hM : IsPairMatching markers)
    (root : Finset V) (hroot : root ∈ markers) (directions : MarkerDirections markers root)
    (e : ↥markers) :
    e.val = {(markerFirst hM root hroot directions e).val,
      (markerLast hM root hroot directions e).val} := pair_eq_endpoints _ _ _

theorem markerFirst_root {markers : Finset (Finset V)} (hM : IsPairMatching markers)
    (root : Finset V) (hroot : root ∈ markers) (directions : MarkerDirections markers root) :
    markerFirst hM root hroot directions ⟨root, hroot⟩ = rootEndpoint hM root hroot := by
  apply Subtype.ext
  simp [markerFirst]

theorem markerFirst_nonroot {markers : Finset (Finset V)} (hM : IsPairMatching markers)
    (root : Finset V) (hroot : root ∈ markers) (directions : MarkerDirections markers root)
    (e : ↥(markers.erase root)) :
    markerFirst hM root hroot directions ⟨e.val, mem_of_mem_erase e.property⟩ = directions e := by
  simp [markerFirst, (mem_erase.mp e.property).1]

/-- Pairwise disjointness identifies a marker from either one of its endpoints. -/
theorem IsPairMatching.eq_of_mem {markers : Finset (Finset V)}
    (hM : IsPairMatching markers) {e f : ↥markers} {v : V}
    (he : v ∈ e.val) (hf : v ∈ f.val) : e = f := by
  apply Subtype.ext
  by_contra hne
  exact disjoint_left.mp (hM.2 e.property f.property hne) he hf

/-- Label the two ports of every marker by its selected orientation. -/
@[expose] def markerEndpointEquiv {markers : Finset (Finset V)} (hM : IsPairMatching markers)
    (root : Finset V) (hroot : root ∈ markers) (directions : MarkerDirections markers root) :
    (↥markers × Bool) ≃ ↥(originalPorts markers) :=
  Equiv.ofBijective (fun p =>
    ⟨if p.2 then (markerLast hM root hroot directions p.1).val
      else (markerFirst hM root hroot directions p.1).val, by
      apply mem_biUnion.mpr
      refine ⟨p.1.val, p.1.property, ?_⟩
      cases p.2 <;> simp only [Bool.false_eq_true, ↓reduceIte]
      · exact (markerFirst hM root hroot directions p.1).property
      · exact (markerLast hM root hroot directions p.1).property⟩) (by
    constructor
    · rintro ⟨e, a⟩ ⟨f, b⟩ heq
      have hv := congrArg Subtype.val heq
      dsimp only at hv
      have heMem : (if a then (markerLast hM root hroot directions e).val
          else (markerFirst hM root hroot directions e).val) ∈ e.val := by
        cases a
        · exact (markerFirst hM root hroot directions e).property
        · exact (markerLast hM root hroot directions e).property
      have hfMem : (if a then (markerLast hM root hroot directions e).val
          else (markerFirst hM root hroot directions e).val) ∈ f.val := by
        rw [hv]
        cases b
        · exact (markerFirst hM root hroot directions f).property
        · exact (markerLast hM root hroot directions f).property
      have hef : e = f := hM.eq_of_mem heMem hfMem
      subst f
      congr 1
      cases a <;> cases b <;> simp only [Bool.false_eq_true, ↓reduceIte] at hv ⊢
      · exact False.elim (markerLast_ne_first hM root hroot directions e hv.symm)
      · exact False.elim (markerLast_ne_first hM root hroot directions e hv)
    · rintro ⟨v, hv⟩
      obtain ⟨e, he, hv⟩ := mem_biUnion.mp hv
      change v ∈ e at hv
      have hp := marker_eq_endpoints hM root hroot directions ⟨e, he⟩
      change e = _ at hp
      rw [hp] at hv
      simp only [mem_insert, mem_singleton] at hv
      rcases hv with hv | hv
      · refine ⟨(⟨e, he⟩, false), ?_⟩
        apply Subtype.ext
        exact hv.symm
      · refine ⟨(⟨e, he⟩, true), ?_⟩
        apply Subtype.ext
        exact hv.symm)

/-- Reassociate expanded marker endpoints and ordinary junction labels. -/
@[expose] def expandedLabelEquiv (markers : Finset (Finset V)) (J : Finset V) :
    ((↥markers ⊕ ↥J) ⊕ ↥markers) ≃ ((↥markers × Bool) ⊕ ↥J) where
  toFun
    | .inl (.inl e) => .inl (e, false)
    | .inl (.inr v) => .inr v
    | .inr e => .inl (e, true)
  invFun
    | .inl (e, false) => .inl (.inl e)
    | .inl (e, true) => .inr e
    | .inr v => .inl (.inr v)
  left_inv x := by rcases x with (e | v) | e <;> rfl
  right_inv x := by rcases x with ⟨e, a⟩ | v; cases a <;> rfl; rfl

/-- Join disjoint original ports and ordinary junctions as actual vertices. -/
@[expose] def portsJunctionEquiv {markers : Finset (Finset V)} {J : Finset V}
    (hJ : J ⊆ univ \ originalPorts markers) :
    (↥(originalPorts markers) ⊕ ↥J) ≃ ↥(originalPorts markers ∪ J) :=
  Equiv.ofBijective (fun x => match x with
    | .inl v => ⟨v.val, mem_union_left _ v.property⟩
    | .inr v => ⟨v.val, mem_union_right _ v.property⟩) (by
      constructor
      · intro a b hab
        have hv := congrArg Subtype.val hab
        rcases a with a | a <;> rcases b with b | b
        · exact congrArg Sum.inl (Subtype.ext hv)
        · exact False.elim ((mem_sdiff.mp (hJ b.property)).2 (hv ▸ a.property))
        · exact False.elim ((mem_sdiff.mp (hJ a.property)).2 (hv.symm ▸ b.property))
        · exact congrArg Sum.inr (Subtype.ext hv)
      · rintro ⟨v, hv⟩
        rcases mem_union.mp hv with hv | hv
        · exact ⟨.inl ⟨v, hv⟩, rfl⟩
        · exact ⟨.inr ⟨v, hv⟩, rfl⟩)

/-- The expanded abstract labels are precisely the actual junction vertices. -/
@[expose] def expandedJunctionEquiv {markers : Finset (Finset V)} (hM : IsPairMatching markers)
    (root : Finset V) (hroot : root ∈ markers) (directions : MarkerDirections markers root)
    (J : Finset V) (hJ : J ⊆ univ \ originalPorts markers) :
    ((↥markers ⊕ ↥J) ⊕ ↥markers) ≃ ↥(originalPorts markers ∪ J) :=
  (expandedLabelEquiv markers J).trans
    ((Equiv.sumCongr (markerEndpointEquiv hM root hroot directions) (Equiv.refl _)).trans
      (portsJunctionEquiv hJ))

end LooseHamilton
