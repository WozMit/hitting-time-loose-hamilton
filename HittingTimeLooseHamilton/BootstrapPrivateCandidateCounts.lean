module

public import HittingTimeLooseHamilton.FrameCompletionRestrictionInjection
public import HittingTimeLooseHamilton.BootstrapPrivateCandidateLifting
public import HittingTimeLooseHamilton.BootstrapFilteredBaseHost

public section

/-! Item 33.15.3: actual ambient directed candidates inject into the
unrestricted residual private-migration summand, with the original filter fixed. -/
noncomputable section
namespace LooseHamilton.BootstrapPrivateCandidateCounts
open Finset BootstrapBases
variable {V : Type} [Fintype V] [DecidableEq V]
variable {r : ℕ} {M : Finset (Finset V)}

theorem source_active_subset_base (b : Base M) (F : AuxiliaryFrame.Frame r M)
    (P : Finset ↥(active b))
    (hd : F.val.deleted = deleted b ∪ liftEdge (active b) P) :
    F.active ⊆ active b := by
  change univ \ F.val.deleted ⊆ univ \ deleted b
  rw [hd]
  intro w hw
  exact mem_sdiff.mpr ⟨mem_univ _,fun hwD =>
    (mem_sdiff.mp hw).2 (mem_union_left _ hwD)⟩

/-- Both completions use precisely the vertices outside D, S, R, x and t. -/
theorem restricted_candidate_active (b : Base M) (F : AuxiliaryFrame.Frame r M)
    (S R : Finset ↥(active b)) (x t : ↥(active b))
    (hd : F.val.deleted = deleted b ∪ liftEdge (active b) (insert x S)) :
    restrictEdge (active b) (F.active \ liftEdge (active b) (insert t R)) =
      univ \ (insert t S ∪ insert x R) := by
  have he : F.active \ liftEdge (active b) (insert t R) =
      univ \ (deleted b ∪ liftEdge (active b) (insert x S ∪ insert t R)) := by
    change (univ \ F.val.deleted) \ _ = _
    rw [hd, liftEdge_union]
    ext w
    simp only [mem_sdiff,mem_univ,mem_union,true_and]
    tauto
  rw [he, BootstrapBaseSourceDictionary.restrict_base_active, restrict_liftEdge]
  ext w
  simp only [mem_sdiff,mem_univ,mem_union,mem_insert,true_and]
  tauto

theorem restricted_candidate_markers (hM : IsPairMatching M) (b : Base M)
    (F : AuxiliaryFrame.Frame r M) (q : Finset ↥(active b)) (u v : ↥(active b))
    (hm : F.markers = insert (liftEdge (active b) q) (markers hM b)) :
    restrictEdges (active b) (insert {u.val,v.val} F.markers) =
      insert {u,v} (insert q (restrictEdges (active b) (markers hM b))) := by
  rw [hm, ← liftEdge_pair]
  simp only [restrictEdges,image_insert,restrict_liftEdge]

/-- Forget directions and apply the injective restriction map. The host here
is the fixed original-port filtered base host for an arbitrary ambient H. -/
theorem completionCount_le_base_summand (hM : IsPairMatching M) (b : Base M)
    (F : AuxiliaryFrame.Frame r M) (hr : 3 ≤ r) (H : SimpleHypergraph V)
    {S q A R : Finset ↥(active b)} {x t u v : ↥(active b)}
    (h : PrivateRootSplitLegal r (restrictEdges (active b) (markers hM b))
      (allowedEdges r (fixedPorts b)) S q x t A R {u,v})
    (hd : F.val.deleted = deleted b ∪ liftEdge (active b) (insert x S))
    (hm : F.markers = insert (liftEdge (active b) q) (markers hM b)) :
    F.completionCount H (liftEdge (active b) (insert t R),u.val,v.val) ≤
      privateMigrationSummand r (restrictEdges (active b) (markers hM b))
        (host r H b) (insert t S) q x (R,{u,v}) := by
  have hc := F.completionCount_le_restricted H
    (liftEdge (active b) (insert t R),u.val,v.val) (active b)
    (source_active_subset_base b F (insert x S) hd)
  dsimp only [Prod.fst,Prod.snd] at hc
  rw [restricted_candidate_active b F S R x t hd,
    restricted_candidate_markers hM b F q u v hm] at hc
  exact hc.trans_eq (cycleOnCount_eq_unrestricted hr _ _ _
    (privateMigration_markers_survive h.target_legal h.split_legal))

/-- Literal summand in the registered test on a uniform ambient host. -/
theorem completionCount_le_registered_summand (hM : IsPairMatching M) (b : Base M)
    (F : AuxiliaryFrame.Frame r M) (hr : 3 ≤ r) (H : SimpleHypergraph V)
    (hH : H ⊆ completeEdges V r)
    {S q A R : Finset ↥(active b)} {x t u v : ↥(active b)}
    (h : PrivateRootSplitLegal r (restrictEdges (active b) (markers hM b))
      (allowedEdges r (fixedPorts b)) S q x t A R {u,v})
    (hd : F.val.deleted = deleted b ∪ liftEdge (active b) (insert x S))
    (hm : F.markers = insert (liftEdge (active b) q) (markers hM b)) :
    F.completionCount H (liftEdge (active b) (insert t R),u.val,v.val) ≤
      privateCandidateCompletionCount r (restrictEdges (active b) (markers hM b))
        (fixedPortHost (inducedHost (active b) H) (fixedPorts b))
        S q x (insert t R,u,v) := by
  rw [privateCandidateCompletionCount_eq_summand]
  simpa only [host_eq_fixedPortHost b H hH] using
    completionCount_le_base_summand hM b F hr H h hd hm

end LooseHamilton.BootstrapPrivateCandidateCounts
