module

public import HittingTimeLooseHamilton.RootFreeCountInvariance
public import HittingTimeLooseHamilton.EndpointSplicing
public import HittingTimeLooseHamilton.RootSamplingModels

public section

/-! Root-free endpoint link tests, indexed by all geometric labels before any
count-based selection. Ordinary-edge prohibition uses the fixed original ports.
The candidate root edge is inserted counterfactually for the structural test;
its membership in the observed host is never consulted. -/
noncomputable section
namespace LooseHamilton
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

abbrev RootFreeEndpointLabel (V : Type*) := EndpointCutLabelI V ⊕ EndpointCutLabelII V

@[expose] def rootFreeEndpointX (r : ℕ) (M G : Finset (Finset V)) (P : Finset V)
    (y z : V) : RootFreeEndpointLabel V → ℕ
  | .inl l => (endpointCutCoreFamilyI r M (rootFreeEdges y G) P y z l).card
  | .inr l => (endpointCutCoreFamilyII r M (rootFreeEdges y G) P y z l).card

@[expose] def rootFreeEndpointY (r : ℕ) (M G : Finset (Finset V)) (P : Finset V)
    (y z t : V) : RootFreeEndpointLabel V → EndpointSpliceInnerLabel V → ℕ
  | .inl l => fun q => endpointSpliceYI r M (rootFreeEdges y G) P y z t l q
  | .inr l => fun q => endpointSpliceYII r M (rootFreeEdges y G) P y z t l q

/-- All structural legal splits of a candidate edge. The edge is tested in a
counterfactual host, and its equality with the reconstructed edge is explicit. -/
@[expose] def RootFreeEndpointSplit (r : ℕ) (M G : Finset (Finset V)) (P : Finset V)
    (y z t : V) (e : Finset V) : RootFreeEndpointLabel V → EndpointSpliceInnerLabel V → Prop
  | .inl l => fun q => {y,q.2} ∪ q.1 = e ∧
      EndpointSpliceLegalI r M (insert e (rootFreeEdges y G)) P y z t l q
  | .inr l => fun q => {y,q.2} ∪ q.1 = e ∧
      EndpointSpliceLegalII r M (insert e (rootFreeEdges y G)) P y z t l q

/-- A bad root edge has no legal split reaching the directed source scale.
Forbidden edges, and edges having no structural legal split, are bad. -/
@[expose] def rootFreeEndpointBadSet (r : ℕ) (M G : Finset (Finset V)) (P U : Finset V)
    (y z t : V) (l : RootFreeEndpointLabel V) (c μ : ℝ) : Finset (Finset V) := by
  classical
  exact (rootEdgeUniverse r y).filter (fun e => e ∉ allowedEdges r U ∨
    ∀ q, RootFreeEndpointSplit r M G P y z t e l q →
      (rootFreeEndpointY r M G P y z t l q : ℝ) <
        c * rootFreeEndpointX r M G P y z l / μ)

/-- The complete test is constant on each root-free observation fiber. -/
theorem rootFreeEndpointBadSet_congr (r : ℕ) (M G H : Finset (Finset V))
    (P U : Finset V) (y z t : V) (l : RootFreeEndpointLabel V) (c μ : ℝ)
    (h : rootFreeEdges y G = rootFreeEdges y H) :
    rootFreeEndpointBadSet r M G P U y z t l c μ =
      rootFreeEndpointBadSet r M H P U y z t l c μ := by
  classical
  unfold rootFreeEndpointBadSet
  apply filter_congr
  intro e _
  cases l <;> simp only [RootFreeEndpointSplit, rootFreeEndpointX, rootFreeEndpointY, h]

/-- The source scale is itself root-free, not merely the final test. -/
theorem rootFreeEndpointX_congr (r : ℕ) (M G H : Finset (Finset V))
    (P : Finset V) (y z : V) (l : RootFreeEndpointLabel V)
    (h : rootFreeEdges y G = rootFreeEdges y H) :
    rootFreeEndpointX r M G P y z l = rootFreeEndpointX r M H P y z l := by
  cases l <;> simp only [rootFreeEndpointX, h]

/-- Root deletion does not alter the actual Type I core count. -/
theorem rootFreeEndpointX_I_eq (r : ℕ) (M G : Finset (Finset V)) (P : Finset V)
    (y z : V) (l : EndpointCutLabelI V) :
    rootFreeEndpointX r M G P y z (.inl l) = (endpointCutCoreFamilyI r M G P y z l).card := by
  simp only [rootFreeEndpointX]
  unfold endpointCutCoreFamilyI
  rw [cycleOnFamily_rootFreeEdges r _ _ G y (by simp [EndpointCutLabelI.deleted])]

/-- Root deletion does not alter the actual Type II core count. -/
theorem rootFreeEndpointX_II_eq (r : ℕ) (M G : Finset (Finset V)) (P : Finset V)
    (y z : V) (l : EndpointCutLabelII V) :
    rootFreeEndpointX r M G P y z (.inr l) = (endpointCutCoreFamilyII r M G P y z l).card := by
  simp only [rootFreeEndpointX]
  unfold endpointCutCoreFamilyII
  rw [cycleOnFamily_rootFreeEdges r _ _ G y (by simp [EndpointCutLabelII.deleted])]

/-- The prescribed Type I directed completion is the actual count in `G`. -/
theorem rootFreeEndpointY_I_eq (r : ℕ) (M G : Finset (Finset V)) (P : Finset V)
    (y z t : V) (l : EndpointCutLabelI V) (q : EndpointSpliceInnerLabel V) :
    rootFreeEndpointY r M G P y z t (.inl l) q = endpointSpliceYI r M G P y z t l q := by
  simp only [rootFreeEndpointY]
  unfold endpointSpliceYI endpointSpliceInputFamilyI
  rw [directedCycleOnFamily_rootFreeEdges r _ _ G _ _ _ _ y
    (by simp [EndpointCutLabelI.deleted])]

/-- The prescribed Type II directed completion is the actual count in `G`. -/
theorem rootFreeEndpointY_II_eq (r : ℕ) (M G : Finset (Finset V)) (P : Finset V)
    (y z t : V) (l : EndpointCutLabelII V) (q : EndpointSpliceInnerLabel V) :
    rootFreeEndpointY r M G P y z t (.inr l) q = endpointSpliceYII r M G P y z t l q := by
  simp only [rootFreeEndpointY]
  unfold endpointSpliceYII endpointSpliceInputFamilyII
  rw [directedCycleOnFamily_rootFreeEdges r _ _ G _ _ _ _ y
    (by simp [EndpointCutLabelII.deleted])]

/-- A good registered edge supplies an actual directed split at the required
scale, including legality in the counterfactual host. -/
theorem rootFreeEndpoint_good_split (r : ℕ) (M G : Finset (Finset V))
    (P U : Finset V) (y z t : V) (l : RootFreeEndpointLabel V) (c μ : ℝ)
    (e : Finset V) (he : e ∈ rootEdgeUniverse r y)
    (hgood : e ∉ rootFreeEndpointBadSet r M G P U y z t l c μ) :
    e ∈ allowedEdges r U ∧ ∃ q, RootFreeEndpointSplit r M G P y z t e l q ∧
      c * rootFreeEndpointX r M G P y z l / μ ≤ (rootFreeEndpointY r M G P y z t l q : ℝ) := by
  classical
  simp only [rootFreeEndpointBadSet, mem_filter, he, true_and, not_or,
    not_not, not_forall, not_lt] at hgood
  obtain ⟨hallowed, q, hq⟩ := hgood
  obtain ⟨hlegal, hbound⟩ := hq
  exact ⟨hallowed, q, hlegal, hbound⟩

omit [Fintype V] in
/-- Once the candidate edge is observed present, the counterfactual Type I
split is legal in the actual host. No other root edge was used by the test. -/
theorem rootFreeEndpointSplit_I_actual (r : ℕ) (M G : Finset (Finset V))
    (P : Finset V) (y z t : V) (e : Finset V) (l : EndpointCutLabelI V)
    (q : EndpointSpliceInnerLabel V) (he : e ∈ G)
    (h : RootFreeEndpointSplit r M G P y z t e (.inl l) q) :
    EndpointSpliceLegalI r M G P y z t l q := by
  exact { h.2 with edge_mem := by rw [h.1]; exact he }

omit [Fintype V] in
/-- Counterfactual Type II splits likewise become actual legal splices. -/
theorem rootFreeEndpointSplit_II_actual (r : ℕ) (M G : Finset (Finset V))
    (P : Finset V) (y z t : V) (e : Finset V) (l : EndpointCutLabelII V)
    (q : EndpointSpliceInnerLabel V) (he : e ∈ G)
    (h : RootFreeEndpointSplit r M G P y z t e (.inr l) q) :
    EndpointSpliceLegalII r M G P y z t l q := by
  exact { h.2 with edge_mem := by rw [h.1]; exact he }

end LooseHamilton
