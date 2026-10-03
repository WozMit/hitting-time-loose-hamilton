module

public import HittingTimeLooseHamilton.BootstrapPrivateLowCapture
public import HittingTimeLooseHamilton.LiftedPrivateObservation

public section

/-! Exact registered lifted private bad sets and reconstruction of their
noncolliding edges from captured ambient candidates. -/
noncomputable section
namespace LooseHamilton.BootstrapPrivateLiftedBadSet
open Finset BootstrapBases
variable {V : Type} [Fintype V] [DecidableEq V]
variable {r : ℕ} {M : Finset (Finset V)}
attribute [local instance] Classical.propDecidable

@[expose] def registeredBadSet (r h time : ℕ) (hM : IsPairMatching M) (b : Base M)
    (S q : Finset ↥(active b)) (x t : ↥(active b)) (J H : SimpleHypergraph V) :=
  ((registerPrivateRootTest r h time (restrictEdges (active b) (markers hM b))
    S q (fixedPorts b) x t (BootstrapConstants.rootThreshold r)).liftDeleted (deleted b)).badSet (J,H)

theorem observation_eq (h time : ℕ) (hM : IsPairMatching M) (b : Base M)
    (S q : Finset ↥(active b)) (x t : ↥(active b)) (J H : SimpleHypergraph V) :
    registeredBadSet r h time hM b S q x t (rootFreeEdges x.val J) (rootFreeEdges x.val H) =
      registeredBadSet r h time hM b S q x t J H :=
  lifted_private_observation r h time (deleted b) _ J H S q (fixedPorts b) x t _

theorem restrictEdge_erase (B : Finset V) (e : Finset V) (x : ↥B) :
    restrictEdge B (e.erase x.val) = (restrictEdge B e).erase x := by
  ext v
  simp [mem_erase, Subtype.val_injective.eq_iff]

theorem rootEdge_lift (B : Finset V) (x t u v : ↥B) (Q : Finset ↥B) :
    privateCandidateRootEdge x.val t.val (liftEdge B Q,u.val,v.val) =
      liftEdge B (privateCandidateRootEdge x t (Q,u,v)) := by
  simp only [privateCandidateRootEdge, Prod.fst, Prod.snd, liftEdge, image_union,
    image_insert, image_singleton, image_erase Subtype.val_injective]

/-- Reconstruction gives an exact ambient edge, not just its restriction. -/
theorem candidate_reconstruct (b : Base M) {S q R : Finset ↥(active b)}
    {x t u v : ↥(active b)} {e : Finset V} (hM : IsPairMatching M)
    (he : e ∈ rootEdgeUniverse r x.val) (hs : e ⊆ active b)
    (h : PrivateRootSplitLegal r (restrictEdges (active b) (markers hM b))
      (allowedEdges r (fixedPorts b)) S q x t
      (restrictEdge (active b) (e.erase x.val)) R {u,v}) :
    privateCandidateRootEdge x.val t.val (liftEdge (active b) (insert t R),u.val,v.val) = e := by
  rw [rootEdge_lift, h.candidate_reconstruct]
  have hi (A : Finset ↥(active b)) : liftEdge (active b) (insert x A) =
      insert x.val (liftEdge (active b) A) := by simp [liftEdge]
  rw [hi, lift_restrictEdge _ _ ((erase_subset _ _).trans hs),
    insert_erase ((mem_rootEdgeUniverse _ _ _).mp he).2]

/-- Intermediate inclusion for any collision set with proved geometric coverage.
The actual geometric coverage is supplied in BootstrapPrivateLiftedDensity. -/
theorem subset_fiber_image_union (h time : ℕ) (hM : IsPairMatching M) (b : Base M)
    (F : AuxiliaryFrame.Frame r M) (hr : 3 ≤ r) (J H : SimpleHypergraph V)
    (hH : H ⊆ completeEdges V r) (S q : Finset ↥(active b)) (x t : ↥(active b))
    (hd : F.val.deleted = deleted b ∪ liftEdge (active b) (insert x S))
    (hm : F.markers = insert (liftEdge (active b) q) (markers hM b))
    (hrel : F.val.relative = none) (ht : t.val ∉ originalPorts M)
    (hW : 0 < completionCount r (restrictEdges (active b) (markers hM b))
      (fixedPortHost (inducedHost (active b) H) (fixedPorts b)) (insert x S) q)
    (α : ℝ) (hα : α ≤ 1/2) (collisions : SimpleHypergraph V)
    (hgeometry : ∀ e ∈ rootEdgeUniverse r x.val, e ∉ collisions →
      e ⊆ active b ∧ ∃ R uv,
        PrivateRootSplitLegal r (restrictEdges (active b) (markers hM b))
          (allowedEdges r (fixedPorts b)) S q x t
          (restrictEdge (active b) (e.erase x.val)) R uv) :
    registeredBadSet r h time hM b S q x t J H ⊆
      (privateBadCandidateFiber (frameAbnormalCandidates F H α) t.val).image
        (privateCandidateRootEdge x.val t.val) ∪ collisions := by
  intro e he
  by_cases hc : e ∈ collisions
  · exact mem_union_right _ hc
  have heroot : e ∈ rootEdgeUniverse r x.val := (mem_filter.mp he).1
  obtain ⟨hs,R,uv,hlegal⟩ := hgeometry e heroot hc
  have htest := ((registerPrivateRootTest r h time
    (restrictEdges (active b) (markers hM b)) S q (fixedPorts b) x t
    (BootstrapConstants.rootThreshold r)).liftDeleted_surviving
      (deleted b) (J,H) e heroot hs).mp he
  obtain ⟨u,v,_,huv⟩ := card_eq_two.mp hlegal.split_legal.pair_card
  subst uv
  have hlegal' : PrivateRootSplitLegal r (restrictEdges (active b) (markers hM b))
      (allowedEdges r (fixedPorts b)) S q x t
      ((restrictEdge (active b) e).erase x) R {u,v} := by
    simpa only [restrictEdge_erase] using hlegal
  have hlow := (mem_filter.mp htest).2 R {u,v} hlegal'
  rw [← privateCandidateCompletionCount_eq_summand] at hlow
  have hcap := BootstrapPrivateLowCapture.low_count_is_abnormal hM b F hr H hH
    hlegal hd hm hrel ht hW α hα hlow
  have hfiber := BootstrapPrivateLowCapture.captured_mem_fiber b F H α R t u v hcap
  exact mem_union_left _ (mem_image.mpr ⟨_,hfiber,candidate_reconstruct b hM heroot hs hlegal⟩)

end LooseHamilton.BootstrapPrivateLiftedBadSet
