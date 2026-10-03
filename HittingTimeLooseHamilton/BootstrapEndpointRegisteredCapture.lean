module

public import HittingTimeLooseHamilton.BootstrapEndpointResidualCounts
public import HittingTimeLooseHamilton.BootstrapEndpointCandidateLifting
public import HittingTimeLooseHamilton.BootstrapEndpointLowCapture

public section

/-! Literal endpoint test summands are captured by actual core-frame imbalance. -/
noncomputable section
namespace LooseHamilton.BootstrapEndpointRegisteredCapture
open Finset BootstrapBases
variable {V : Type} [Fintype V] [DecidableEq V]
variable {r : ℕ} {M : Finset (Finset V)}

/-- Exact registered Type I source count on either original base. -/
theorem source_I (hM : IsPairMatching M) (b : Base M)
    (F : AuxiliaryFrame.Frame r M) (H : SimpleHypergraph V)
    (hH : H ⊆ completeEdges V r) (P : Finset ↥(active b))
    (y z : ↥(active b)) (l : EndpointCutLabelI ↥(active b))
    (hd : F.val.deleted = deleted b ∪ liftEdge (active b) (P ∪ l.deleted y))
    (hm : F.markers = (l.markers (restrictEdges (active b) (markers hM b)) z).image
      (liftEdge (active b)))
    (hrel : F.val.relative = none) :
    F.cycleCount H = rootFreeEndpointX r (restrictEdges (active b) (markers hM b))
      (fixedPortHost (inducedHost (active b) H) (fixedPorts b)) P y z (.inl l) := by
  rw [rootFreeEndpointX_I_eq]
  exact BootstrapEndpointResidualCounts.core_count b F H hH _ _ hd hm hrel

/-- Exact Type I summand: both directed starts use the same cycle witness. -/
theorem summand_I (hM : IsPairMatching M) (b : Base M)
    (F : AuxiliaryFrame.Frame r M) (H : SimpleHypergraph V)
    (hH : H ⊆ completeEdges V r) (P : Finset ↥(active b))
    (y z : ↥(active b)) (l : EndpointCutLabelI ↥(active b))
    (hd : F.val.deleted = deleted b ∪ liftEdge (active b) (P ∪ l.deleted y))
    (hm : F.markers = (l.markers (restrictEdges (active b) (markers hM b)) z).image
      (liftEdge (active b)))
    (hroot : F.val.root = (l.1.val,z.val)) (hrel : F.val.relative = none)
    (t : ↥(active b)) (q : EndpointSpliceInnerLabel ↥(active b))
    (hc : F.LegalCandidate (liftEdge (active b) q.1,q.2.val,t.val)) :
    F.completionCount H (liftEdge (active b) q.1,q.2.val,t.val) = rootFreeEndpointY r (restrictEdges (active b) (markers hM b))
      (fixedPortHost (inducedHost (active b) H) (fixedPorts b)) P y z t (.inl l) q := by
  rw [rootFreeEndpointY_I_eq]
  exact BootstrapEndpointResidualCounts.completion_count b F H hH _ _ _ _ _ _ _
    (mem_insert_self _ _) hd hm hroot hrel hc

/-- A low literal Type I summand is abnormal at the fixed registry threshold.
Candidate legality, count dictionaries and favorable mean are all derived. -/
theorem low_summand_I (hM : IsPairMatching M) (b : Base M)
    (F : AuxiliaryFrame.Frame r M) (H : SimpleHypergraph V)
    (hH : H ⊆ completeEdges V r) (P : Finset ↥(active b))
    (y z : ↥(active b)) (l : EndpointCutLabelI ↥(active b))
    (hd : F.val.deleted = deleted b ∪ liftEdge (active b) (P ∪ l.deleted y))
    (hm : F.markers = (l.markers (restrictEdges (active b) (markers hM b)) z).image
      (liftEdge (active b)))
    (hr : 3 ≤ r) (hroot : F.val.root = (l.1.val,z.val))
    (hrel : F.val.relative = none) (G : SimpleHypergraph ↥(active b))
    (t : ↥(active b)) (q : EndpointSpliceInnerLabel ↥(active b))
    (h : EndpointSpliceLegalI r (restrictEdges (active b) (markers hM b)) G P y z t l q)
    (he : {y,q.2} ∪ q.1 ∈ allowedEdges r (fixedPorts b)) (ht : t ∉ fixedPorts b)
    (hX : 0 < rootFreeEndpointX r (restrictEdges (active b) (markers hM b))
      (fixedPortHost (inducedHost (active b) H) (fixedPorts b)) P y z (.inl l))
    (α : ℝ) (hα : α ≤ 1/2)
    (hlow : (rootFreeEndpointY r (restrictEdges (active b) (markers hM b))
      (fixedPortHost (inducedHost (active b) H) (fixedPorts b)) P y z t (.inl l) q : ℝ) <
      (1 / (2 * ((r:ℝ)-1)^2)) * (rootFreeEndpointX r (restrictEdges (active b) (markers hM b))
      (fixedPortHost (inducedHost (active b) H) (fixedPorts b)) P y z (.inl l) : ℝ) /
        rootFreeEndpointMean r (inducedHost (active b) H) P y (.inl l)) :
    (liftEdge (active b) q.1,q.2.val,t.val) ∈ frameAbnormalCandidates F H α := by
  have hc := BootstrapEndpointCandidateLifting.candidate_I hM b F hr G P y z t l q hd hm h he ht
  have hs := source_I hM b F H hH P y z l hd hm hrel
  have hy := summand_I hM b F H hH P y z l hd hm hroot hrel t q hc
  apply BootstrapEndpointLowCapture.low_count_is_abnormal b F hr H P y (.inl l) hd _ hc
    (by rw [hs]; exact hX) α hα
  simpa only [hy,hs] using hlow

/-- Exact registered Type II source count on either original base. -/
theorem source_II (hM : IsPairMatching M) (b : Base M)
    (F : AuxiliaryFrame.Frame r M) (H : SimpleHypergraph V)
    (hH : H ⊆ completeEdges V r) (P : Finset ↥(active b))
    (y z : ↥(active b)) (l : EndpointCutLabelII ↥(active b))
    (hd : F.val.deleted = deleted b ∪ liftEdge (active b) (P ∪ l.deleted y))
    (hm : F.markers = (l.markers (restrictEdges (active b) (markers hM b)) z).image
      (liftEdge (active b)))
    (hrel : F.val.relative = none) :
    F.cycleCount H = rootFreeEndpointX r (restrictEdges (active b) (markers hM b))
      (fixedPortHost (inducedHost (active b) H) (fixedPorts b)) P y z (.inr l) := by
  rw [rootFreeEndpointX_II_eq]
  exact BootstrapEndpointResidualCounts.core_count b F H hH _ _ hd hm hrel

/-- Exact Type II summand: both directed starts use the same cycle witness. -/
theorem summand_II (hM : IsPairMatching M) (b : Base M)
    (F : AuxiliaryFrame.Frame r M) (H : SimpleHypergraph V)
    (hH : H ⊆ completeEdges V r) (P : Finset ↥(active b))
    (y z : ↥(active b)) (l : EndpointCutLabelII ↥(active b))
    (hd : F.val.deleted = deleted b ∪ liftEdge (active b) (P ∪ l.deleted y))
    (hm : F.markers = (l.markers (restrictEdges (active b) (markers hM b)) z).image
      (liftEdge (active b)))
    (hroot : F.val.root = (l.2.2.1.val,z.val)) (hrel : F.val.relative = none)
    (t : ↥(active b)) (q : EndpointSpliceInnerLabel ↥(active b))
    (hc : F.LegalCandidate (liftEdge (active b) q.1,q.2.val,t.val)) :
    F.completionCount H (liftEdge (active b) q.1,q.2.val,t.val) = rootFreeEndpointY r (restrictEdges (active b) (markers hM b))
      (fixedPortHost (inducedHost (active b) H) (fixedPorts b)) P y z t (.inr l) q := by
  rw [rootFreeEndpointY_II_eq]
  exact BootstrapEndpointResidualCounts.completion_count b F H hH _ _ _ _ _ _ _
    (mem_insert_self _ _) hd hm hroot hrel hc

/-- A low literal Type II summand is abnormal at the fixed registry threshold.
Candidate legality, count dictionaries and favorable mean are all derived. -/
theorem low_summand_II (hM : IsPairMatching M) (b : Base M)
    (F : AuxiliaryFrame.Frame r M) (H : SimpleHypergraph V)
    (hH : H ⊆ completeEdges V r) (P : Finset ↥(active b))
    (y z : ↥(active b)) (l : EndpointCutLabelII ↥(active b))
    (hd : F.val.deleted = deleted b ∪ liftEdge (active b) (P ∪ l.deleted y))
    (hm : F.markers = (l.markers (restrictEdges (active b) (markers hM b)) z).image
      (liftEdge (active b)))
    (hr : 3 ≤ r) (hroot : F.val.root = (l.2.2.1.val,z.val))
    (hrel : F.val.relative = none) (G : SimpleHypergraph ↥(active b))
    (t : ↥(active b)) (q : EndpointSpliceInnerLabel ↥(active b))
    (h : EndpointSpliceLegalII r (restrictEdges (active b) (markers hM b)) G P y z t l q)
    (he : {y,q.2} ∪ q.1 ∈ allowedEdges r (fixedPorts b)) (ht : t ∉ fixedPorts b)
    (hX : 0 < rootFreeEndpointX r (restrictEdges (active b) (markers hM b))
      (fixedPortHost (inducedHost (active b) H) (fixedPorts b)) P y z (.inr l))
    (α : ℝ) (hα : α ≤ 1/2)
    (hlow : (rootFreeEndpointY r (restrictEdges (active b) (markers hM b))
      (fixedPortHost (inducedHost (active b) H) (fixedPorts b)) P y z t (.inr l) q : ℝ) <
      (1 / (2 * ((r:ℝ)-1)^2)) * (rootFreeEndpointX r (restrictEdges (active b) (markers hM b))
      (fixedPortHost (inducedHost (active b) H) (fixedPorts b)) P y z (.inr l) : ℝ) /
        rootFreeEndpointMean r (inducedHost (active b) H) P y (.inr l)) :
    (liftEdge (active b) q.1,q.2.val,t.val) ∈ frameAbnormalCandidates F H α := by
  have hc := BootstrapEndpointCandidateLifting.candidate_II hM b F hr G P y z t l q hd hm h he ht
  have hs := source_II hM b F H hH P y z l hd hm hrel
  have hy := summand_II hM b F H hH P y z l hd hm hroot hrel t q hc
  apply BootstrapEndpointLowCapture.low_count_is_abnormal b F hr H P y (.inr l) hd _ hc
    (by rw [hs]; exact hX) α hα
  simpa only [hy,hs] using hlow

end LooseHamilton.BootstrapEndpointRegisteredCapture
