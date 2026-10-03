module

public import HittingTimeLooseHamilton.LiftedRootTestSampling
public import HittingTimeLooseHamilton.RootEventGoodLinks

public section

/-! Good lifted edges inject into the residual good edges. The resulting
lower bound uses the ambient degree, with no residual sampling assumption. -/
noncomputable section
namespace LooseHamilton
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem RegisteredRootTest.liftDeleted_good_card_le {r h : ℕ}
    (D : Finset V) (test : RegisteredRootTest ↥(univ \ D) r h)
    (F H : SimpleHypergraph V) (hH : H ⊆ completeEdges V r) :
    (rootGoodEdges H ((test.liftDeleted D).badSet (F,H)) test.root.val).card ≤
      (rootGoodEdges (inducedHost (univ \ D) H)
        (test.badSet (inducedHost (univ \ D) F, inducedHost (univ \ D) H)) test.root).card := by
  classical
  let E := rootGoodEdges H ((test.liftDeleted D).badSet (F,H)) test.root.val
  have hs : ∀ e ∈ E, e ⊆ univ \ D := by
    intro e he
    obtain ⟨he,hn⟩ := mem_sdiff.mp he
    obtain ⟨heH,hx⟩ := mem_filter.mp he
    exact ((test.liftDeleted_good D (F,H) e
      ((mem_rootEdgeUniverse _ _ _).mpr ⟨(mem_completeEdges _ _).mp (hH heH),hx⟩)).mp hn).1
  have hi : Set.InjOn (restrictEdge (univ \ D)) (↑E : Set (Finset V)) := by
    intro e he f hf hh
    have hh' := congrArg (liftEdge (univ \ D)) hh
    simpa only [lift_restrictEdge _ _ (hs e he),lift_restrictEdge _ _ (hs f hf)] using hh'
  have hsub : E.image (restrictEdge (univ \ D)) ⊆
      rootGoodEdges (inducedHost (univ \ D) H)
        (test.badSet (inducedHost (univ \ D) F, inducedHost (univ \ D) H)) test.root := by
    intro a ha
    obtain ⟨e,he,rfl⟩ := mem_image.mp ha
    obtain ⟨he',hn⟩ := mem_sdiff.mp he
    obtain ⟨heH,hx⟩ := mem_filter.mp he'
    have heU : e ∈ rootEdgeUniverse r test.root.val :=
      (mem_rootEdgeUniverse _ _ _).mpr ⟨(mem_completeEdges _ _).mp (hH heH),hx⟩
    refine mem_sdiff.mpr ⟨mem_filter.mpr ⟨?_,(mem_restrictEdge _ _ _).mpr hx⟩,?_⟩
    · rw [mem_inducedHost, ambientEdge_eq_liftEdge, lift_restrictEdge _ _ (hs e he)]
      exact heH
    · exact ((test.liftDeleted_good D (F,H) e heU).mp hn).2
  calc
    E.card = (E.image (restrictEdge (univ \ D))).card := (card_image_of_injOn hi).symm
    _ ≤ _ := card_le_card hsub

theorem RegisteredRootTest.liftDeleted_good_card_lower {r h : ℕ}
    (D : Finset V) (test : RegisteredRootTest ↥(univ \ D) r h)
    (F H : SimpleHypergraph V) (hH : H ⊆ completeEdges V r)
    (hn : ¬ RootLinkBad ((test.liftDeleted D).badSet (F,H))
      (vertexDegree H test.root.val) (F,H)) :
    (vertexDegree H test.root.val : ℝ)/3 ≤
      (rootGoodEdges (inducedHost (univ \ D) H)
        (test.badSet (inducedHost (univ \ D) F, inducedHost (univ \ D) H)) test.root).card := by
  exact (rootGoodEdges_card_lower r F H _ _ ((test.liftDeleted D).bad_subset _) hn).trans
    (Nat.cast_le.mpr (test.liftDeleted_good_card_le D F H hH))

end LooseHamilton
