module

public import HittingTimeLooseHamilton.DirectedCompletions

public section

noncomputable section
namespace LooseHamilton
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

@[expose] def relabelEdges (σ : Equiv.Perm V) (E : Finset (Finset V)) := E.image (Finset.image σ)

@[expose] def relabelEdgeEquiv (σ : Equiv.Perm V) (E : Finset (Finset V)) :
    ↥E ≃ ↥(relabelEdges σ E) := Equiv.ofBijective
  (fun e => ⟨e.val.image σ, mem_image_of_mem _ e.property⟩) (by
    constructor
    · intro a b h
      exact Subtype.ext ((Finset.image_injective σ.injective) (congrArg Subtype.val h))
    · rintro ⟨e,he⟩
      obtain ⟨a,ha,rfl⟩ := mem_image.mp he
      exact ⟨⟨a,ha⟩,rfl⟩)

namespace MixedCycleWitness
variable {r : ℕ} {markers edges : Finset (Finset V)}
@[expose] def relabel (C : MixedCycleWitness r markers edges) (σ : Equiv.Perm V)
    (hM : ∀ m ∈ markers, m.image σ = m) :
    MixedCycleWitness r markers (relabelEdges σ edges) := by
  let ee := relabelEdgeEquiv σ edges
  refine {
    length := C.length
    length_ge := C.length_ge
    junction := fun i => σ (C.junction i)
    junction_injective := σ.injective.comp C.junction_injective
    junction_next_ne := fun i h => C.junction_next_ne i (σ.injective h)
    slot := C.slot.trans (Equiv.sumCongr (Equiv.refl _) ee)
    privateBlock := fun e => (C.privateBlock (ee.symm e)).image σ
    private_card := ?_
    private_disjoint := ?_
    junction_private_disjoint := ?_
    cover := ?_
    marked_matching := C.marked_matching
    slot_edge := ?_ }
  · intro e
    rw [card_image_of_injective _ σ.injective]
    exact C.private_card _
  · intro e f hef
    exact (disjoint_image σ.injective).mpr (C.private_disjoint (fun h => hef (ee.symm.injective h)))
  · intro e
    change Disjoint (univ.image (σ ∘ C.junction)) _
    rw [← image_image]
    exact (disjoint_image σ.injective).mpr (C.junction_private_disjoint _)
  · have h := congrArg (Finset.image σ) C.cover
    have hu : (univ : Finset V).image σ = univ := by ext x; simp
    rw [hu, image_union, image_image] at h
    rw [h]
    congr 1
    ext x
    simp only [mem_image, mem_biUnion, mem_univ, true_and]
    constructor
    · rintro ⟨v, ⟨e,he⟩, hv⟩
      exact ⟨ee e, v, by simpa using he, hv⟩
    · rintro ⟨e,v,hv,hx⟩
      exact ⟨v, ⟨ee.symm e,hv⟩,hx⟩
  · intro i
    have hs := C.slot_edge i
    cases hi : C.slot i with
    | inl m =>
      simp only [Equiv.trans_apply, Equiv.sumCongr_apply, hi, Equiv.refl_apply]
      rw [hi] at hs
      have h := congrArg (Finset.image σ) hs
      simpa [hM m.val m.property] using h
    | inr e =>
      simp only [Equiv.trans_apply, Equiv.sumCongr_apply, hi]
      rw [hi] at hs
      have h := congrArg (Finset.image σ) hs
      simpa [ee, relabelEdgeEquiv, image_union] using h

theorem relabel_markerStart (C : MixedCycleWitness r markers edges) (σ : Equiv.Perm V)
    (hM : ∀ m ∈ markers, m.image σ = m) (m : ↥markers) :
    ((C.relabel σ hM).markerStart m).val = σ (C.markerStart m).val := by
  have hs : (C.relabel σ hM).slot.symm (.inl m) = C.slot.symm (.inl m) := by
    apply (C.relabel σ hM).slot.injective
    rw [Equiv.apply_symm_apply]
    change _ = (Equiv.sumCongr (Equiv.refl _) (relabelEdgeEquiv σ edges))
      (C.slot (C.slot.symm (.inl m)))
    rw [Equiv.apply_symm_apply]
    rfl
  change σ (C.junction ((C.relabel σ hM).slot.symm (.inl m))) = _
  rw [hs]
  rfl
end MixedCycleWitness
end LooseHamilton
