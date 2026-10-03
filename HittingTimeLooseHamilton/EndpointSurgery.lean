module

public import HittingTimeLooseHamilton.EndpointIndex

public section

/-! Restricting the junctions and private blocks of a mixed cycle.

The input to `compress` contains only the changed slots and the surviving
vertex equation. All uniqueness, uniformity and disjointness assertions are
inherited from the source cycle.
-/
noncomputable section
namespace LooseHamilton
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace MixedCycleOnWitness
variable {r : ℕ} {S : Finset V} {markers edges : Finset (Finset V)}

/-- Compress a cyclic path, keeping all private blocks of surviving edges.
The index and slot maps record the actual splice, rather than assuming the
existence of an output cycle. -/
@[expose] def compress (C : MixedCycleOnWitness r S markers edges)
    {S' : Finset V} {markers' edges' : Finset (Finset V)}
    (m : ℕ) (hm : 3 ≤ m)
    (keep : Fin m ↪ Fin C.length)
    (hE : edges' ⊆ edges)
    (slot' : Fin m ≃ (↥markers' ⊕ ↥edges'))
    (hmatch : (markers' : Set (Finset V)).PairwiseDisjoint id)
    (hcover : S' = univ.image (C.junction ∘ keep) ∪
      univ.biUnion (fun e : ↥edges' => C.privateBlock ⟨e.val, hE e.property⟩))
    (hslot : ∀ i, match slot' i with
      | Sum.inl e => e.val = {C.junction (keep i), C.junction (keep (finRotate m i))}
      | Sum.inr e => e.val = {C.junction (keep i), C.junction (keep (finRotate m i))} ∪
        C.privateBlock ⟨e.val, hE e.property⟩) :
    MixedCycleOnWitness r S' markers' edges' where
  length := m
  length_ge := hm
  junction := C.junction ∘ keep
  junction_injective := C.junction_injective.comp keep.injective
  junction_next_ne := by
    intro i he
    have hi := keep.injective (C.junction_injective he)
    have hv := congrArg Fin.val hi
    rw [finRotate_val_eq m (by omega)] at hv
    split_ifs at hv <;> omega
  slot := slot'
  privateBlock e := C.privateBlock ⟨e.val, hE e.property⟩
  private_card e := C.private_card _
  private_disjoint := by
    intro e f hef
    apply C.private_disjoint
    intro heq
    exact hef (Subtype.ext (congrArg (fun e : ↥edges => e.val) heq))
  junction_private_disjoint e := by
    apply (C.junction_private_disjoint ⟨e.val, hE e.property⟩).mono_left
    intro v hv
    obtain ⟨i, _, rfl⟩ := mem_image.mp hv
    exact mem_image_of_mem C.junction (mem_univ (keep i))
  cover := hcover
  marked_matching := hmatch
  slot_edge := hslot

@[simp] theorem compress_privateBlock
    (C : MixedCycleOnWitness r S markers edges)
    {S' : Finset V} {markers' edges' : Finset (Finset V)}
    (m : ℕ) (hm : 3 ≤ m) (keep : Fin m ↪ Fin C.length)
    (hE : edges' ⊆ edges)
    (slot' : Fin m ≃ (↥markers' ⊕ ↥edges'))
    (hmatch : (markers' : Set (Finset V)).PairwiseDisjoint id)
    (hcover : S' = univ.image (C.junction ∘ keep) ∪
      univ.biUnion (fun e : ↥edges' => C.privateBlock ⟨e.val, hE e.property⟩))
    (hslot : ∀ i, match slot' i with
      | Sum.inl e => e.val = {C.junction (keep i), C.junction (keep (finRotate m i))}
      | Sum.inr e => e.val = {C.junction (keep i), C.junction (keep (finRotate m i))} ∪
        C.privateBlock ⟨e.val, hE e.property⟩)
    (e : ↥edges') :
    (C.compress m hm keep hE slot' hmatch hcover hslot).privateBlock e =
      C.privateBlock ⟨e.val, hE e.property⟩ := rfl

/-- The surviving private union is the original union minus the removed
private union. Disjointness comes from the original cycle, even if some of
its private blocks are empty. -/
theorem retained_private_union (C : MixedCycleOnWitness r S markers edges)
    (removed : Finset (Finset V)) :
    univ.biUnion (fun e : ↥(edges \ removed) =>
      C.privateBlock ⟨e.val, (mem_sdiff.mp e.property).1⟩) =
    (univ.biUnion C.privateBlock) \
      univ.biUnion (fun e : ↥(edges ∩ removed) =>
        C.privateBlock ⟨e.val, (mem_inter.mp e.property).1⟩) := by
  ext v
  simp only [mem_sdiff, mem_biUnion, mem_univ, true_and]
  constructor
  · rintro ⟨e, he⟩
    refine ⟨⟨⟨e.val, (mem_sdiff.mp e.property).1⟩, he⟩, ?_⟩
    rintro ⟨f, hf⟩
    have hne : (⟨e.val, (mem_sdiff.mp e.property).1⟩ : ↥edges) ≠
        ⟨f.val, (mem_inter.mp f.property).1⟩ := by
      intro heq
      have hev := congrArg Subtype.val heq
      exact (mem_sdiff.mp e.property).2 (hev ▸ (mem_inter.mp f.property).2)
    exact disjoint_left.mp (C.private_disjoint hne) he hf
  · rintro ⟨⟨e, he⟩, hn⟩
    have her : e.val ∉ removed := by
      intro her
      exact hn ⟨⟨e.val, mem_inter.mpr ⟨e.property, her⟩⟩, he⟩
    exact ⟨⟨e.val, mem_sdiff.mpr ⟨e.property, her⟩⟩, he⟩
end MixedCycleOnWitness
end LooseHamilton
