module

public import HittingTimeLooseHamilton.VertexRelabel
public import HittingTimeLooseHamilton.BiasedRoleStatement

public section

noncomputable section
namespace LooseHamilton
open Finset
variable {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]

@[expose] def vertexEdges (σ : V ≃ W) (E : Finset (Finset V)) := E.image (Finset.image σ)

@[expose] def vertexEdgeEquiv (σ : V ≃ W) (E : Finset (Finset V)) :
    ↥E ≃ ↥(vertexEdges σ E) := Equiv.ofBijective
  (fun e => ⟨e.val.image σ, mem_image_of_mem _ e.property⟩) (by
    constructor
    · intro a b h
      exact Subtype.ext ((Finset.image_injective σ.injective) (congrArg Subtype.val h))
    · rintro ⟨e,he⟩
      obtain ⟨a,ha,rfl⟩ := mem_image.mp he
      exact ⟨⟨a,ha⟩,rfl⟩)

namespace MixedCycleWitness
variable {r : ℕ} {markers edges : Finset (Finset V)}
@[expose] def relabelVia (C : MixedCycleWitness r markers edges) (σ : V ≃ W)
 :
    MixedCycleWitness r (vertexEdges σ markers) (vertexEdges σ edges) := by
  let me := vertexEdgeEquiv σ markers
  let ee := vertexEdgeEquiv σ edges
  refine {
    length := C.length
    length_ge := C.length_ge
    junction := fun i => σ (C.junction i)
    junction_injective := σ.injective.comp C.junction_injective
    junction_next_ne := fun i h => C.junction_next_ne i (σ.injective h)
    slot := C.slot.trans (Equiv.sumCongr me ee)
    privateBlock := fun e => (C.privateBlock (ee.symm e)).image σ
    private_card := ?_
    private_disjoint := ?_
    junction_private_disjoint := ?_
    cover := ?_
    marked_matching := ?_
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
  · intro a ha b hb hab
    change a ∈ vertexEdges σ markers at ha
    change b ∈ vertexEdges σ markers at hb
    unfold vertexEdges at ha hb
    obtain ⟨a0,ha0,rfl⟩ := mem_image.mp ha
    obtain ⟨b0,hb0,rfl⟩ := mem_image.mp hb
    exact (disjoint_image σ.injective).mpr (C.marked_matching ha0 hb0 (fun h => hab (congrArg _ h)))
  · intro i
    have hs := C.slot_edge i
    cases hi : C.slot i with
    | inl m =>
      simp only [Equiv.trans_apply, Equiv.sumCongr_apply, hi]
      rw [hi] at hs
      have h := congrArg (Finset.image σ) hs
      simpa [me, vertexEdgeEquiv] using h
    | inr e =>
      simp only [Equiv.trans_apply, Equiv.sumCongr_apply, hi]
      rw [hi] at hs
      have h := congrArg (Finset.image σ) hs
      simpa [ee, vertexEdgeEquiv, image_union] using h

private theorem relabelVia_inverse_slot (C : MixedCycleWitness r markers edges) (σ : V ≃ W)
    (x : ↥markers ⊕ ↥edges) :
    (C.relabelVia σ).slot.symm
      ((Equiv.sumCongr (vertexEdgeEquiv σ markers) (vertexEdgeEquiv σ edges)) x) =
      C.slot.symm x := by
  apply (C.relabelVia σ).slot.injective
  rw [Equiv.apply_symm_apply]
  change _ = (Equiv.sumCongr (vertexEdgeEquiv σ markers) (vertexEdgeEquiv σ edges))
    (C.slot (C.slot.symm x))
  rw [Equiv.apply_symm_apply]

@[simp] theorem relabelVia_markerStart (C : MixedCycleWitness r markers edges) (σ : V ≃ W)
    (m : ↥markers) :
    ((C.relabelVia σ).markerStart (vertexEdgeEquiv σ markers m)).val =
      σ (C.markerStart m).val := by
  change σ (C.junction ((C.relabelVia σ).slot.symm
    ((Equiv.sumCongr (vertexEdgeEquiv σ markers) (vertexEdgeEquiv σ edges)) (.inl m)))) = _
  rw [relabelVia_inverse_slot]
  rfl

@[simp] theorem relabelVia_slot_start (C : MixedCycleWitness r markers edges) (σ : V ≃ W)
    (e : ↥edges) :
    (C.relabelVia σ).junction ((C.relabelVia σ).slot.symm
      (.inr (vertexEdgeEquiv σ edges e))) = σ (C.junction (C.slot.symm (.inr e))) := by
  change σ (C.junction ((C.relabelVia σ).slot.symm
    ((Equiv.sumCongr (vertexEdgeEquiv σ markers) (vertexEdgeEquiv σ edges)) (.inr e)))) = _
  rw [relabelVia_inverse_slot]

@[simp] theorem relabelVia_slot_end (C : MixedCycleWitness r markers edges) (σ : V ≃ W)
    (e : ↥edges) :
    (C.relabelVia σ).junction (finRotate (C.relabelVia σ).length
      ((C.relabelVia σ).slot.symm (.inr (vertexEdgeEquiv σ edges e)))) =
        σ (C.junction (finRotate C.length (C.slot.symm (.inr e)))) := by
  change σ (C.junction (finRotate C.length ((C.relabelVia σ).slot.symm
    ((Equiv.sumCongr (vertexEdgeEquiv σ markers) (vertexEdgeEquiv σ edges)) (.inr e))))) = _
  rw [relabelVia_inverse_slot]
end MixedCycleWitness
end LooseHamilton
