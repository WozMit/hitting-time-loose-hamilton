module

public import HittingTimeLooseHamilton.Cycles

public section

/-! # Mixed cycles on an active vertex set

The ambient vertices stay fixed while a surgery changes the active set.  The
cover equation, rather than a new dependent vertex type, records that set.
-/
namespace LooseHamilton
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

structure MixedCycleOnWitness (r : ℕ) (S : Finset V) (markers edges : Finset (Finset V)) where
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
  cover : S = univ.image junction ∪ univ.biUnion privateBlock
  marked_matching : (markers : Set (Finset V)).PairwiseDisjoint id
  slot_edge : ∀ i, match slot i with
    | Sum.inl e => e.val = {junction i, junction (finRotate length i)}
    | Sum.inr e => e.val = {junction i, junction (finRotate length i)} ∪ privateBlock e

@[expose] def IsMixedCycleOn (r : ℕ) (S : Finset V) (markers edges : Finset (Finset V)) : Prop :=
  Nonempty (MixedCycleOnWitness r S markers edges)

namespace MixedCycleOnWitness
variable {r : ℕ} {S : Finset V} {markers edges : Finset (Finset V)}

theorem junction_mem (C : MixedCycleOnWitness r S markers edges) (i : Fin C.length) :
    C.junction i ∈ S := by
  have h : C.junction i ∈ univ.image C.junction ∪ univ.biUnion C.privateBlock := mem_union_left _ (mem_image_of_mem _ (mem_univ _))
  exact (congrArg (fun T : Finset V => C.junction i ∈ T) C.cover).mpr h

theorem private_subset_active (C : MixedCycleOnWitness r S markers edges)
    (e : {e // e ∈ edges}) : C.privateBlock e ⊆ S := by
  intro v hv
  rw [C.cover]
  exact mem_union_right _ (mem_biUnion.mpr ⟨e, mem_univ _, hv⟩)

theorem marked_subset_active (C : MixedCycleOnWitness r S markers edges)
    {e : Finset V} (he : e ∈ markers) : e ⊆ S := by
  have h := C.slot_edge (C.slot.symm (.inl ⟨e, he⟩))
  rw [C.slot.apply_symm_apply] at h
  simp only at h
  rw [h]
  exact insert_subset_iff.mpr ⟨C.junction_mem _, singleton_subset_iff.mpr (C.junction_mem _)⟩

theorem edge_subset_active (C : MixedCycleOnWitness r S markers edges)
    {e : Finset V} (he : e ∈ edges) : e ⊆ S := by
  have h := C.slot_edge (C.slot.symm (.inr ⟨e, he⟩))
  rw [C.slot.apply_symm_apply] at h
  simp only at h
  rw [h]
  exact union_subset (insert_subset_iff.mpr ⟨C.junction_mem _, singleton_subset_iff.mpr (C.junction_mem _)⟩)
    (C.private_subset_active _)

@[expose] def toSpanning (C : MixedCycleOnWitness r univ markers edges) :
    MixedCycleWitness r markers edges :=
  { C with }
end MixedCycleOnWitness

@[expose] def MixedCycleWitness.onUniv {r : ℕ} {markers edges : Finset (Finset V)}
    (C : MixedCycleWitness r markers edges) : MixedCycleOnWitness r univ markers edges :=
  { C with }

theorem isMixedCycleOn_univ_iff {r : ℕ} {markers edges : Finset (Finset V)} :
    IsMixedCycleOn r univ markers edges ↔ IsMixedCycle r markers edges :=
  ⟨fun ⟨C⟩ => ⟨C.toSpanning⟩, fun ⟨C⟩ => ⟨C.onUniv⟩⟩
end LooseHamilton
