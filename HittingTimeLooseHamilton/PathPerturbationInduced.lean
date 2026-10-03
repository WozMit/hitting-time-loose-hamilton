module

public import HittingTimeLooseHamilton.PathPerturbationBasic

public section

noncomputable section
namespace LooseHamilton
open Finset
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]

lemma pairDegree_restrictEdges (S : Finset V) (G : SimpleHypergraph V)
    (hG : ∀ e ∈ G, e ⊆ S) (v w : ↥S) :
    pairDegree (restrictEdges S G) v w = pairDegree G v.val w.val := by
  unfold pairDegree
  symm
  apply card_bij (fun e _ => restrictEdge S e)
  · intro e he
    obtain ⟨he,hv,hw⟩ := mem_filter.mp he
    exact mem_filter.mpr ⟨mem_image_of_mem _ he,by simpa using hv,by simpa using hw⟩
  · intro e he f hf h
    have hh := congrArg (liftEdge S) h
    simpa only [lift_restrictEdge S e (hG e (mem_filter.mp he).1),
      lift_restrictEdge S f (hG f (mem_filter.mp hf).1)] using hh
  · intro e he
    obtain ⟨he,hv,hw⟩ := mem_filter.mp he
    obtain ⟨f,hf,rfl⟩ := mem_image.mp he
    exact ⟨f,mem_filter.mpr ⟨hf,by simpa using hv,by simpa using hw⟩,rfl⟩

lemma pairDegree_deleteVertices (F : SimpleHypergraph V) (Z : Finset V)
    (v w : ↥(univ \ Z)) :
    pairDegree (deleteVertices Z F) v w = pairDegree (survivingHost F Z) v.val w.val := by
  change pairDegree (inducedHost (univ \ Z) F) v w = pairDegree (coreOutside Z F) _ _
  rw [← restricted_core_eq_inducedHost]
  apply pairDegree_restrictEdges
  intro e he x hx
  exact mem_sdiff.mpr ⟨mem_univ _, fun hz =>
    disjoint_left.mp ((mem_coreOutside _ _ _).mp he).2 hx hz⟩

lemma filter_restrictEdges_card (S : Finset V) (G : SimpleHypergraph V)
    (hG : ∀ e ∈ G, e ⊆ S) (P : Finset V → Prop) [DecidablePred P] :
    ((restrictEdges S G).filter (fun e => P (liftEdge S e))).card = (G.filter P).card := by
  symm
  apply card_bij (fun e _ => restrictEdge S e)
  · intro e he
    obtain ⟨he,hp⟩ := mem_filter.mp he
    exact mem_filter.mpr ⟨mem_image_of_mem _ he,by simpa [lift_restrictEdge S e (hG e he)] using hp⟩
  · intro e he f hf h
    have hh := congrArg (liftEdge S) h
    simpa only [lift_restrictEdge S e (hG e (mem_filter.mp he).1),
      lift_restrictEdge S f (hG f (mem_filter.mp hf).1)] using hh
  · intro e he
    obtain ⟨he,hp⟩ := mem_filter.mp he
    obtain ⟨f,hf,rfl⟩ := mem_image.mp he
    exact ⟨f,mem_filter.mpr ⟨hf,by simpa [lift_restrictEdge S f (hG f hf)] using hp⟩,rfl⟩

lemma liftEdge_inter (S : Finset V) (e A : Finset ↥S) :
    liftEdge S (e ∩ A) = liftEdge S e ∩ liftEdge S A := by
  apply Finset.image_inter
  exact Subtype.val_injective

/-- Partition counts on the induced vertex subtype equal ambient counts with
its partition lifted back to the original vertex universe. -/
lemma induced_partition_count (F : SimpleHypergraph V) (Z : Finset V)
    (A : Finset ↥(univ \ Z)) :
    ((deleteVertices Z F).filter (fun e => (e ∩ A).card = 2)).card =
      ((survivingHost F Z).filter (fun e => (e ∩ liftEdge (univ \ Z) A).card = 2)).card := by
  have hp : ∀ e : Finset ↥(univ \ Z),
      (e ∩ A).card = (liftEdge (univ \ Z) e ∩ liftEdge (univ \ Z) A).card := by
    intro e
    rw [← liftEdge_inter, liftEdge_card]
  simp_rw [hp]
  change ((inducedHost (univ \ Z) F).filter _).card = ((coreOutside Z F).filter _).card
  rw [← restricted_core_eq_inducedHost]
  apply filter_restrictEdges_card (univ \ Z) (coreOutside Z F) _
    (fun e => (e ∩ liftEdge (univ \ Z) A).card = 2)
  intro e he x hx
  exact mem_sdiff.mpr ⟨mem_univ _, fun hz =>
    disjoint_left.mp ((mem_coreOutside _ _ _).mp he).2 hx hz⟩

end LooseHamilton
