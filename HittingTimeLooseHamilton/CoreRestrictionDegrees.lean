module

public import HittingTimeLooseHamilton.CycleOnCounting

public section

/-! Cardinality and vertex-degree preservation under restriction to active vertices. -/
noncomputable section
namespace LooseHamilton
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Restricting edges supported on the active set preserves their number. -/
theorem restrictEdges_card_of_supported (S : Finset V) (G : SimpleHypergraph V)
    (hG : ∀ e ∈ G, e ⊆ S) : (restrictEdges S G).card = G.card := by
  have h := Fintype.card_congr (restrictedEdgeEquiv S G hG)
  simpa only [Fintype.card_coe] using h.symm

/-- Restricting supported edges preserves every surviving vertex degree. -/
theorem vertexDegree_restrictEdges (S : Finset V) (G : SimpleHypergraph V)
    (hG : ∀ e ∈ G, e ⊆ S) (v : ↥S) :
    vertexDegree (restrictEdges S G) v = vertexDegree G v.val := by
  unfold vertexDegree
  symm
  apply card_bij (fun e _ => restrictEdge S e)
  · intro e he
    obtain ⟨he,hv⟩ := mem_filter.mp he
    exact mem_filter.mpr ⟨mem_image_of_mem _ he,(mem_restrictEdge _ _ _).mpr hv⟩
  · intro e he f hf h
    have hh := congrArg (liftEdge S) h
    simpa only [lift_restrictEdge S e (hG e (mem_filter.mp he).1),
      lift_restrictEdge S f (hG f (mem_filter.mp hf).1)] using hh
  · intro e he
    obtain ⟨he,hv⟩ := mem_filter.mp he
    obtain ⟨f,hf,rfl⟩ := mem_image.mp he
    exact ⟨f,mem_filter.mpr ⟨hf,(mem_restrictEdge _ _ _).mp hv⟩,rfl⟩

theorem vertexDegree_liftEdges (S : Finset V) (G : SimpleHypergraph ↥S) (v : ↥S) :
    vertexDegree (G.image (liftEdge S)) v.val = vertexDegree G v := by
  have hs : ∀ e ∈ G.image (liftEdge S), e ⊆ S := by
    intro e he
    obtain ⟨f,_,rfl⟩ := mem_image.mp he
    exact liftEdge_subset S f
  have h := vertexDegree_restrictEdges S (G.image (liftEdge S)) hs v
  rw [restrictEdges_liftEdges] at h
  exact h.symm

end LooseHamilton
