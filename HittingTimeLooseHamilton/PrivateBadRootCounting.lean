module

public import HittingTimeLooseHamilton.RootTestRegistrations
public import HittingTimeLooseHamilton.PrivateMigrationTargets

public section

/-! Bad private root edges inject into bad directed candidates, after removing
structurally invalid labels. The reconstruction map makes the target-coordinate
multiplicity and the separate geometric collision error explicit. -/
noncomputable section
namespace LooseHamilton
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
attribute [local instance] Classical.propDecidable

/-- Root edges with no structural private split. This is a deterministic set
of geometric labels, independent of the observed graph and its counts. -/
@[expose] def privateRootInvalidEdges (r : ℕ) (markers allowed : SimpleHypergraph V)
    (S q : Finset V) (x t : V) : SimpleHypergraph V :=
  (rootEdgeUniverse r x).filter fun e =>
    ¬ ∃ R uv, PrivateRootSplitLegal r markers allowed S q x t (e.erase x) R uv

/-- Reconstruction of a root edge from a candidate incident to target `t`. -/
@[expose] def privateCandidateRootEdge (x t : V) (a : Finset V × V × V) : Finset V :=
  {a.2.1,a.2.2} ∪ insert x (a.1.erase t)

/-- The structural split has no target in its remainder, so reconstruction
of its directed candidate recovers the proposed root edge exactly. -/
theorem PrivateRootSplitLegal.candidate_reconstruct {r : ℕ}
    {markers allowed : SimpleHypergraph V} {S q A R : Finset V} {x t u v : V}
    (h : PrivateRootSplitLegal r markers allowed S q x t A R {u,v}) :
    privateCandidateRootEdge x t (insert t R,u,v) = insert x A := by
  have ht : t ∉ R := by
    intro ht
    exact disjoint_left.mp h.split_legal.forbidden_disjoint
      (mem_union_right _ (mem_insert_of_mem ht)) (mem_union_left _ (mem_insert_self _ _))
  simpa [privateCandidateRootEdge, ht] using mem_singleton.mp h.split_legal.edge_mem

/-- A bad root test supplies a low actual candidate count. Once candidate
balance identifies these low counts with exceptional candidates, the only
additional bad edges are structurally invalid ones. -/
theorem private_bad_root_edges_card_le (r h time : ℕ)
    (markers F H : SimpleHypergraph V) (S q U : Finset V) (x t : V) (c : ℝ)
    (bad : Finset (Finset V × V × V))
    (hcapture : ∀ A R u v,
      PrivateRootSplitLegal r markers (allowedEdges r U) S q x t A R {u,v} →
      (privateCandidateCompletionCount r markers (fixedPortHost H U) S q x
        (insert t R,u,v) : ℝ) <
          c * (completionCount r markers (fixedPortHost H U) (insert x S) q : ℝ) /
            privateRootSourceMean r H S x →
      (insert t R,u,v) ∈ bad) :
    ((registerPrivateRootTest r h time markers S q U x t c).badSet (F,H)).card ≤
      (privateBadCandidateFiber bad t).card +
        (privateRootInvalidEdges r markers (allowedEdges r U) S q x t).card := by
  let Γ := (registerPrivateRootTest r h time markers S q U x t c).badSet (F,H)
  let invalid := privateRootInvalidEdges r markers (allowedEdges r U) S q x t
  have hsub : Γ ⊆ (privateBadCandidateFiber bad t).image (privateCandidateRootEdge x t) ∪ invalid := by
    intro e he
    by_cases hi : e ∈ invalid
    · exact mem_union_right _ hi
    · obtain ⟨heroot,hbad⟩ := mem_filter.mp he
      have hs : ∃ R uv, PrivateRootSplitLegal r markers (allowedEdges r U) S q x t (e.erase x) R uv := by
        have hnot : ¬ ¬ ∃ R uv, PrivateRootSplitLegal r markers (allowedEdges r U) S q x t (e.erase x) R uv := by
          intro hnone
          exact hi (mem_filter.mpr ⟨heroot,hnone⟩)
        exact not_not.mp hnot
      obtain ⟨R,uv,hlegal⟩ := hs
      obtain ⟨u,v,huv,huveq⟩ := card_eq_two.mp hlegal.split_legal.pair_card
      subst uv
      have hlow := hbad R {u,v} hlegal
      rw [← privateCandidateCompletionCount_eq_summand] at hlow
      have hcb := hcapture (e.erase x) R u v hlegal hlow
      apply mem_union_left
      apply mem_image.mpr
      refine ⟨(insert t R,u,v), mem_filter.mpr ⟨hcb,mem_insert_self _ _⟩, ?_⟩
      exact hlegal.candidate_reconstruct.trans
        (insert_erase ((mem_rootEdgeUniverse _ _ _).mp heroot).2)
  exact (card_le_card hsub).trans ((card_union_le _ _).trans
    (Nat.add_le_add_right card_image_le _))

end LooseHamilton
