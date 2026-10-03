module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Logic.Equiv.Fin.Rotate
public import Mathlib.Tactic

public section

/-!
# Connected spanning mixed loose cycles

A witness presents one cyclic order of all junctions. Each slot is occupied exactly once by
either a prescribed marked pair or an ordinary edge. The predicate forgets the presentation;
its arguments are the unoriented edge sets, so rotations and reversals are not counted twice.
The convention of at least three slots excludes degenerate short cycles, as in the manuscript.
-/

namespace LooseHamilton

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- An explicit cyclic presentation. Private vertices are indexed by the ordinary edges.
The disjointness and covering fields express that every vertex is a junction or is private
to exactly one edge. The slot equivalence ensures that precisely the prescribed edges occur. -/
structure MixedCycleWitness (r : ℕ) (markers edges : Finset (Finset V)) where
  length : ℕ
  length_ge : 3 ≤ length
  junction : Fin length → V
  junction_injective : Function.Injective junction
  junction_next_ne : ∀ i, junction i ≠ junction (finRotate length i)
  slot : Fin length ≃ ({e // e ∈ markers} ⊕ {e // e ∈ edges})
  privateBlock : {e // e ∈ edges} → Finset V
  private_card : ∀ e, (privateBlock e).card = r - 2
  private_disjoint : Pairwise (fun e f => Disjoint (privateBlock e) (privateBlock f))
  junction_private_disjoint : ∀ e, Disjoint (univ.image junction) (privateBlock e)
  cover : univ = univ.image junction ∪ univ.biUnion privateBlock
  marked_matching : (markers : Set (Finset V)).PairwiseDisjoint id
  slot_edge : ∀ i, match slot i with
    | Sum.inl e => e.val = {junction i, junction (finRotate length i)}
    | Sum.inr e => e.val = {junction i, junction (finRotate length i)} ∪ privateBlock e

/-- The connected spanning mixed-cycle predicate on ordinary unoriented edge sets. -/
@[expose] def IsMixedCycle (r : ℕ) (markers edges : Finset (Finset V)) : Prop :=
  Nonempty (MixedCycleWitness r markers edges)

namespace MixedCycleWitness

variable {r : ℕ} {markers edges : Finset (Finset V)}

theorem length_eq (C : MixedCycleWitness r markers edges) :
    C.length = markers.card + edges.card := by
  simpa using Fintype.card_congr C.slot

theorem junction_card (C : MixedCycleWitness r markers edges) :
    (univ.image C.junction).card = C.length := by
  rw [card_image_of_injective _ C.junction_injective]
  simp

theorem private_union_card (C : MixedCycleWitness r markers edges) :
    (univ.biUnion C.privateBlock).card = (r - 2) * edges.card := by
  rw [card_biUnion]
  · simp [C.private_card, Nat.mul_comm]
  · intro e _ f _ hef
    exact C.private_disjoint hef

theorem junction_private_union_disjoint (C : MixedCycleWitness r markers edges) :
    Disjoint (univ.image C.junction) (univ.biUnion C.privateBlock) := by
  rw [disjoint_biUnion_right]
  intro e _
  exact C.junction_private_disjoint e

theorem vertex_card (C : MixedCycleWitness r markers edges) (hr : 3 ≤ r) :
    Fintype.card V = (r - 1) * edges.card + markers.card := by
  have hc := congrArg Finset.card C.cover
  rw [card_univ, card_union_of_disjoint C.junction_private_union_disjoint,
    C.junction_card, C.private_union_card, C.length_eq] at hc
  have hstep : r - 1 = (r - 2) + 1 := by omega
  rw [hstep, Nat.add_mul]
  simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hc

theorem marked_card (C : MixedCycleWitness r markers edges) {e : Finset V}
    (he : e ∈ markers) : e.card = 2 := by
  let i := C.slot.symm (Sum.inl ⟨e, he⟩)
  have hs : C.slot i = Sum.inl ⟨e, he⟩ := C.slot.apply_symm_apply _
  have h := C.slot_edge i
  rw [hs] at h
  simp only at h
  rw [h]
  exact card_pair (C.junction_next_ne i)

theorem uniform (C : MixedCycleWitness r markers edges) (hr : 3 ≤ r)
    {e : Finset V} (he : e ∈ edges) : e.card = r := by
  let a : {e // e ∈ edges} := ⟨e, he⟩
  let i := C.slot.symm (Sum.inr a)
  have hs : C.slot i = Sum.inr a := C.slot.apply_symm_apply _
  have h := C.slot_edge i
  rw [hs] at h
  simp only at h
  have hd : Disjoint {C.junction i, C.junction (finRotate C.length i)}
      (C.privateBlock a) := by
    apply (C.junction_private_disjoint a).mono_left
    intro x hx
    simp only [mem_insert, mem_singleton] at hx
    rcases hx with rfl | rfl <;> exact mem_image_of_mem _ (mem_univ _)
  change e = _ at h
  rw [h, card_union_of_disjoint hd, C.private_card]
  simp only [card_pair (C.junction_next_ne i)]
  omega

theorem edges_disjoint_markers (C : MixedCycleWitness r markers edges) (hr : 3 ≤ r) :
    Disjoint edges markers := by
  rw [Finset.disjoint_left]
  intro e he hm
  have := C.uniform hr he
  have := C.marked_card hm
  omega

theorem junction_incident (C : MixedCycleWitness r markers edges) (i : Fin C.length) :
    ∃ e ∈ edges ∪ markers, C.junction i ∈ e := by
  have hs := C.slot_edge i
  cases hi : C.slot i with
  | inl e =>
    rw [hi] at hs
    refine ⟨e.val, mem_union_right _ e.property, ?_⟩
    simp only at hs
    rw [hs]
    simp
  | inr e =>
    rw [hi] at hs
    refine ⟨e.val, mem_union_left _ e.property, ?_⟩
    simp only at hs
    rw [hs]
    simp

theorem private_subset (C : MixedCycleWitness r markers edges) (e : {e // e ∈ edges}) :
    C.privateBlock e ⊆ e.val := by
  have hs := C.slot_edge (C.slot.symm (Sum.inr e))
  rw [C.slot.apply_symm_apply] at hs
  simp only at hs
  rw [hs]
  exact subset_union_right

theorem covers (C : MixedCycleWitness r markers edges) (v : V) :
    ∃ e ∈ edges ∪ markers, v ∈ e := by
  have hv : v ∈ univ.image C.junction ∪ univ.biUnion C.privateBlock := by
    rw [← C.cover]
    exact mem_univ _
  rcases mem_union.mp hv with hj | hp
  · obtain ⟨i, _, rfl⟩ := mem_image.mp hj
    exact C.junction_incident i
  · obtain ⟨e, _, he⟩ := mem_biUnion.mp hp
    exact ⟨e.val, mem_union_left _ e.property, C.private_subset e he⟩

theorem marked_vertices_subset_junctions (C : MixedCycleWitness r markers edges) :
    markers.biUnion id ⊆ univ.image C.junction := by
  intro v hv
  obtain ⟨e, he, hv⟩ := mem_biUnion.mp hv
  let i := C.slot.symm (Sum.inl ⟨e, he⟩)
  have hs : C.slot i = Sum.inl ⟨e, he⟩ := C.slot.apply_symm_apply _
  have h := C.slot_edge i
  rw [hs] at h
  simp only at h
  change v ∈ e at hv
  rw [h] at hv
  simp only [mem_insert, mem_singleton] at hv
  rcases hv with rfl | rfl <;> exact mem_image_of_mem _ (mem_univ _)

theorem marked_vertices_card (C : MixedCycleWitness r markers edges) :
    (markers.biUnion id).card = 2 * markers.card := by
  rw [card_biUnion C.marked_matching]
  calc
    ∑ e ∈ markers, (id e).card = ∑ _e ∈ markers, 2 := by
      apply sum_congr rfl
      intro e he
      exact C.marked_card he
    _ = 2 * markers.card := by simp [Nat.mul_comm]

/-- There are `k-s` junctions outside the marked pairs. -/
theorem ordinary_junction_card (C : MixedCycleWitness r markers edges) :
    (univ.image C.junction \ markers.biUnion id).card = edges.card - markers.card := by
  rw [card_sdiff_of_subset C.marked_vertices_subset_junctions,
    C.junction_card, C.marked_vertices_card, C.length_eq]
  omega

theorem markers_card_le_edges_card (C : MixedCycleWitness r markers edges) :
    markers.card ≤ edges.card := by
  have h := card_le_card C.marked_vertices_subset_junctions
  rw [C.marked_vertices_card, C.junction_card, C.length_eq] at h
  omega

theorem edges_card_pos (C : MixedCycleWitness r markers edges) : 0 < edges.card := by
  have := C.markers_card_le_edges_card
  have := C.length_eq
  have := C.length_ge
  omega

end MixedCycleWitness

namespace IsMixedCycle

variable {r : ℕ} {markers edges : Finset (Finset V)}

theorem vertex_card (h : IsMixedCycle r markers edges) (hr : 3 ≤ r) :
    Fintype.card V = (r - 1) * edges.card + markers.card := by
  obtain ⟨C⟩ := h
  exact C.vertex_card hr

theorem edge_card (h : IsMixedCycle r markers edges) (hr : 3 ≤ r) :
    edges.card = (Fintype.card V - markers.card) / (r - 1) := by
  rw [h.vertex_card hr, Nat.add_sub_cancel]
  have hp : 0 < r - 1 := by omega
  simp [Nat.mul_div_cancel_left, hp]

theorem divisibility (h : IsMixedCycle r markers edges) (hr : 3 ≤ r) :
    r - 1 ∣ Fintype.card V - markers.card := by
  rw [h.vertex_card hr, Nat.add_sub_cancel]
  exact dvd_mul_right _ _

theorem uniform (h : IsMixedCycle r markers edges) (hr : 3 ≤ r) :
    ∀ e ∈ edges, e.card = r := by
  obtain ⟨C⟩ := h
  exact fun _ he => C.uniform hr he

theorem marked_card (h : IsMixedCycle r markers edges) :
    ∀ e ∈ markers, e.card = 2 := by
  obtain ⟨C⟩ := h
  exact fun _ he => C.marked_card he

theorem edges_disjoint_markers (h : IsMixedCycle r markers edges) (hr : 3 ≤ r) :
    Disjoint edges markers := by
  obtain ⟨C⟩ := h
  exact C.edges_disjoint_markers hr

theorem marked_matching (h : IsMixedCycle r markers edges) :
    (markers : Set (Finset V)).PairwiseDisjoint id := by
  obtain ⟨C⟩ := h
  exact C.marked_matching

theorem covers (h : IsMixedCycle r markers edges) (v : V) :
    ∃ e ∈ edges ∪ markers, v ∈ e := by
  obtain ⟨C⟩ := h
  exact C.covers v

theorem markers_card_le_edges_card (h : IsMixedCycle r markers edges) :
    markers.card ≤ edges.card := by
  obtain ⟨C⟩ := h
  exact C.markers_card_le_edges_card

theorem edges_card_pos (h : IsMixedCycle r markers edges) : 0 < edges.card := by
  obtain ⟨C⟩ := h
  exact C.edges_card_pos

end IsMixedCycle
end LooseHamilton
