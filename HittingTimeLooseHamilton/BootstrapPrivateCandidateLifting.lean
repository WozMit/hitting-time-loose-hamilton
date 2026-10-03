module

public import HittingTimeLooseHamilton.PrivateSplitCandidateGeometry
public import HittingTimeLooseHamilton.PrivateCompletionLifting
public import HittingTimeLooseHamilton.BootstrapActualSourceFrames

public section

/-! Item 33.15.2: a residual split is a legal candidate of the actual
ambient source frame. Neither edge presence nor a positive cycle count is
required. All forbidden ports are inherited from the original matching. -/
noncomputable section
namespace LooseHamilton.BootstrapPrivateCandidateLifting
open Finset BootstrapBases
variable {V : Type} [Fintype V] [DecidableEq V]
variable {r : ℕ} {M : Finset (Finset V)}

/-- Transport candidate legality from the residual base to an ambient source
frame whose deleted set is exactly the base deletion and current private block. -/
theorem candidate_of_geometry (hM : IsPairMatching M) (b : Base M)
    (F : AuxiliaryFrame.Frame r M) (P q Q : Finset ↥(active b))
    (u v : ↥(active b))
    (hd : F.val.deleted = deleted b ∪ liftEdge (active b) P)
    (hm : F.markers = insert (liftEdge (active b) q) (markers hM b))
    (hc : LegalPrivateCompletion r
      (insert q (restrictEdges (active b) (markers hM b))) Q {u,v})
    (hs : Q ∪ {u,v} ⊆ univ \ P)
    (ha : Q ∪ {u,v} ∈ allowedEdges r (fixedPorts b)) :
    F.LegalCandidate (liftEdge (active b) Q, u.val, v.val) := by
  have hc' : LegalPrivateCompletion r
      (restrictEdges (active b) (insert (liftEdge (active b) q) (markers hM b)))
      Q {u,v} := by
    simpa only [restrictEdges, image_insert, restrict_liftEdge] using hc
  refine ⟨?_, ?_, ?_⟩
  · rw [hm]
    simpa only [liftEdge_pair] using hc'.lift
  · change liftEdge (active b) Q ∪ {u.val,v.val} ⊆ univ \ F.val.deleted
    rw [hd, ← liftEdge_pair, ← liftEdge_union]
    intro w hw
    obtain ⟨a, ha, rfl⟩ := mem_image.mp hw
    refine mem_sdiff.mpr ⟨mem_univ _, ?_⟩
    intro hx
    rcases mem_union.mp hx with hD | hP
    · exact (mem_sdiff.mp a.property).2 hD
    · have hap : a ∈ restrictEdge (active b) (liftEdge (active b) P) :=
        (mem_restrictEdge _ _ a).mpr hP
      exact (mem_sdiff.mp (hs ha)).2 (by simpa only [restrict_liftEdge] using hap)
  · rw [← liftEdge_pair, ← liftEdge_union]
    exact (liftEdge_mem_allowed_iff r (active b) (originalPorts M) _).mpr ha

/-- A structurally legal residual split lifts to a legal ambient candidate.
In particular, the theorem includes r = 3 (an empty rest block) and does not
assume that the counterfactual root edge occurs in a host. -/
theorem frame_candidate (hM : IsPairMatching M) (b : Base M)
    (F : AuxiliaryFrame.Frame r M) (hr : 3 ≤ r)
    {S q A R : Finset ↥(active b)} {x t u v : ↥(active b)}
    (h : PrivateRootSplitLegal r (restrictEdges (active b) (markers hM b))
      (allowedEdges r (fixedPorts b)) S q x t A R {u,v})
    (hd : F.val.deleted = deleted b ∪ liftEdge (active b) (insert x S))
    (hm : F.markers = insert (liftEdge (active b) q) (markers hM b))
    (ht : t.val ∉ originalPorts M) :
    F.LegalCandidate (liftEdge (active b) (insert t R), u.val, v.val) := by
  have ht' : t ∉ fixedPorts b := fun hp => ht ((mem_fixedPorts b t).mp hp)
  obtain ⟨hc,hs,ha⟩ := h.candidate_geometry hr ht'
  exact candidate_of_geometry hM b F (insert x S) q (insert t R) u v hd hm hc hs ha

end LooseHamilton.BootstrapPrivateCandidateLifting
