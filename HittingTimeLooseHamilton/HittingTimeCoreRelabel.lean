module

public import HittingTimeLooseHamilton.VertexEquivInvariants
public import HittingTimeLooseHamilton.Counting

public section

noncomputable section
namespace LooseHamilton.HittingTimeCore
open Finset
variable {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]

omit [Fintype V] [Fintype W] in
@[simp] theorem vertexEdges_symm (σ : V ≃ W) (H : SimpleHypergraph V) :
    vertexEdges σ.symm (vertexEdges σ H) = H := by
  unfold vertexEdges
  rw [image_image]
  have he : (image σ.symm ∘ image σ) = id := by
    funext e
    simp [Function.comp_def,image_image]
  rw [he, image_id]

omit [Fintype V] [DecidableEq V] [Fintype W] in
theorem vertexEdges_mono (σ : V ≃ W) {H G : SimpleHypergraph V} (h : H ⊆ G) :
    vertexEdges σ H ⊆ vertexEdges σ G := image_subset_image h

omit [Fintype V] [Fintype W] in
@[simp] theorem ports_vertexEdges (σ : V ≃ W) (markers : SimpleHypergraph V) :
    originalPorts (vertexEdges σ markers) = (originalPorts markers).image σ := by
  ext x
  constructor
  · intro hx
    obtain ⟨e,he,hx⟩ := mem_biUnion.mp hx
    obtain ⟨a,ha,rfl⟩ := mem_image.mp he
    obtain ⟨v,hv,rfl⟩ := mem_image.mp hx
    exact mem_image.mpr ⟨v,mem_biUnion.mpr ⟨a,ha,hv⟩,rfl⟩
  · intro hx
    obtain ⟨v,hv,rfl⟩ := mem_image.mp hx
    obtain ⟨a,ha,hv⟩ := mem_biUnion.mp hv
    exact mem_biUnion.mpr ⟨a.image σ,mem_image_of_mem _ ha,mem_image_of_mem _ hv⟩

theorem allowed_image (σ : V ≃ W) (r : ℕ) (ports e : Finset V)
    (he : e ∈ allowedEdges r ports) : e.image σ ∈ allowedEdges r (ports.image σ) := by
  simp only [allowedEdges,mem_filter,mem_completeEdges] at he ⊢
  simpa only [← image_inter _ _ σ.injective,card_image_of_injective _ σ.injective] using he

theorem cycleCount_pos_vertexEdges (σ : V ≃ W) (r : ℕ) (markers H : SimpleHypergraph V)
    (h : 0 < cycleCount r markers H (originalPorts markers)) :
    0 < cycleCount r (vertexEdges σ markers) (vertexEdges σ H)
      (originalPorts (vertexEdges σ markers)) := by
  obtain ⟨C,⟨hC⟩,hH,hallow⟩ := (cycleCount_pos_iff _ _ _ _).mp h
  apply (cycleCount_pos_iff _ _ _ _).mpr
  refine ⟨vertexEdges σ C,⟨hC.relabelVia σ⟩,vertexEdges_mono σ hH,?_⟩
  intro e he
  obtain ⟨a,ha,rfl⟩ := mem_image.mp he
  rw [ports_vertexEdges]
  exact allowed_image σ r _ a (hallow ha)

theorem cycleCount_pos_vertexEdges_iff (σ : V ≃ W) (r : ℕ) (markers H : SimpleHypergraph V) :
    (0 < cycleCount r (vertexEdges σ markers) (vertexEdges σ H)
      (originalPorts (vertexEdges σ markers))) ↔
    0 < cycleCount r markers H (originalPorts markers) := by
  constructor
  · intro h
    simpa using cycleCount_pos_vertexEdges σ.symm r _ _ h
  · exact cycleCount_pos_vertexEdges σ r markers H
end LooseHamilton.HittingTimeCore
