module

public import HittingTimeLooseHamilton.FrameEntropyRelabel
public import HittingTimeLooseHamilton.PathRegularityModels
public import HittingTimeLooseHamilton.VertexRestriction

public section

/-! Vertex equivalences preserve the combinatorial and regularity quantities. -/
noncomputable section
namespace LooseHamilton
open Finset
variable {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]

@[simp] theorem vertexEdges_card (σ : V ≃ W) (E : SimpleHypergraph V) :
    (vertexEdges σ E).card = E.card := by
  exact card_image_of_injective _ (Finset.image_injective σ.injective)

@[simp] theorem vertexEdges_vertexDegree (σ : V ≃ W) (E : SimpleHypergraph V) (v : V) :
    vertexDegree (vertexEdges σ E) (σ v) = vertexDegree E v := by
  unfold vertexDegree vertexEdges
  rw [filter_image]
  simp only [mem_image, σ.injective.eq_iff, exists_eq_right]
  exact card_image_of_injective _ (Finset.image_injective σ.injective)

@[simp] theorem vertexEdges_pairDegree (σ : V ≃ W) (E : SimpleHypergraph V) (u v : V) :
    pairDegree (vertexEdges σ E) (σ u) (σ v) = pairDegree E u v := by
  unfold pairDegree vertexEdges
  rw [filter_image]
  simp only [mem_image, σ.injective.eq_iff, exists_eq_right]
  exact card_image_of_injective _ (Finset.image_injective σ.injective)

@[simp] theorem vertexEdges_partitionCount (σ : V ≃ W) (E : SimpleHypergraph V)
    (A : Finset V) : partitionCount (vertexEdges σ E) (A.image σ) = partitionCount E A := by
  unfold partitionCount vertexEdges
  rw [filter_image]
  simp only [← image_inter _ _ σ.injective, card_image_of_injective _ σ.injective]
  exact card_image_of_injective _ (Finset.image_injective σ.injective)

theorem IsPairMatching.vertexEdges {E : SimpleHypergraph V} (h : IsPairMatching E)
    (σ : V ≃ W) : IsPairMatching (vertexEdges σ E) := by
  constructor
  · intro e he
    obtain ⟨f,hf,rfl⟩ := mem_image.mp he
    simpa [card_image_of_injective _ σ.injective] using h.1 f hf
  · intro e he f hf hef
    obtain ⟨a,ha,rfl⟩ := mem_image.mp he
    obtain ⟨b,hb,rfl⟩ := mem_image.mp hf
    exact (disjoint_image σ.injective).mpr (h.2 ha hb (fun h => hef (congrArg _ h)))

@[simp] theorem vertexEdges_meanDegree (σ : V ≃ W) (r : ℕ) (E : SimpleHypergraph V) :
    meanDegree (V:=W) r (vertexEdges σ E).card = meanDegree (V:=V) r E.card := by
  simp [meanDegree, Fintype.card_congr σ]

theorem PathPartitionRegular.vertexEdges {r : ℕ} {C L : ℝ} {E : SimpleHypergraph V}
    (h : PathPartitionRegular r C L E) (σ : V ≃ W) :
    PathPartitionRegular r C L (vertexEdges σ E) := by
  intro A hA
  have hcard := Fintype.card_congr σ
  have hAA : (A.image σ.symm).image σ = A := by simp [image_image]
  have hA' : |((A.image σ.symm).card:ℝ)-junctionFraction r*Fintype.card V| ≤
      L*(Fintype.card V:ℝ)^(1/10:ℝ) := by simpa [hcard, card_image_of_injective _ σ.symm.injective] using hA
  have hh := h (A.image σ.symm) hA'
  rw [← vertexEdges_partitionCount σ E (A.image σ.symm), hAA] at hh
  simpa [hcard, meanDegree] using hh

theorem PathGraphUpperRegular.vertexEdges {r : ℕ} {C L : ℝ} {E : SimpleHypergraph V}
    (h : PathGraphUpperRegular r C L E) (σ : V ≃ W) :
    PathGraphUpperRegular r C L (vertexEdges σ E) := by
  constructor
  · intro v
    obtain ⟨v,rfl⟩ := σ.surjective v
    simpa [meanDegree, Fintype.card_congr σ] using h.upper_degree v
  · intro u v huv
    obtain ⟨u,rfl⟩ := σ.surjective u
    obtain ⟨v,rfl⟩ := σ.surjective v
    simpa [meanDegree, Fintype.card_congr σ] using h.codegree u v (fun h => huv (congrArg σ h))
  · exact h.partitions.vertexEdges σ

theorem PathGraphRegular.vertexEdges {r : ℕ} {c C L : ℝ} {E : SimpleHypergraph V}
    (h : PathGraphRegular r c C L E) (σ : V ≃ W) :
    PathGraphRegular r c C L (vertexEdges σ E) := by
  refine ⟨h.toPathGraphUpperRegular.vertexEdges σ, ?_⟩
  intro v
  obtain ⟨v,rfl⟩ := σ.surjective v
  simpa [meanDegree, Fintype.card_congr σ] using h.lower_degree v
theorem IsPairMatching.restrictEdges {E : SimpleHypergraph V} (h : IsPairMatching E)
    (S : Finset V) (hS : ∀ e ∈ E, e ⊆ S) : IsPairMatching (restrictEdges S E) := by
  constructor
  · intro e he
    obtain ⟨a,ha,rfl⟩ := mem_image.mp he
    rw [← liftEdge_card, lift_restrictEdge S a (hS a ha)]
    exact h.1 a ha
  · intro e he f hf hef
    obtain ⟨a,ha,rfl⟩ := mem_image.mp he
    obtain ⟨b,hb,rfl⟩ := mem_image.mp hf
    apply (liftEdge_disjoint S _ _).mp
    change Disjoint (liftEdge S (restrictEdge S a)) (liftEdge S (restrictEdge S b))
    rw [lift_restrictEdge S a (hS a ha), lift_restrictEdge S b (hS b hb)]
    exact h.2 ha hb (fun h => hef (congrArg _ h))
end LooseHamilton
