module

public import HittingTimeLooseHamilton.RootTestRegistrations
public import HittingTimeLooseHamilton.BootstrapBases

public section

/-! # Ambient interpretation of residual root tests
Lifting changes the bad-set predicate, not the underlying sampling process.
Time, deficit, root degree and probability space remain ambient.
-/
noncomputable section
namespace LooseHamilton
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

@[simp] theorem RegisteredRootTest.liftDeleted_time {r h : ℕ} (D : Finset V)
    (test : RegisteredRootTest ↥(univ \ D) r h) :
    (test.liftDeleted D).time = test.time := rfl

@[simp] theorem RegisteredRootTest.liftDeleted_root {r h : ℕ} (D : Finset V)
    (test : RegisteredRootTest ↥(univ \ D) r h) :
    (test.liftDeleted D).root = test.root.val := rfl

/-- Every good ambient root edge survives and is good for the residual test. -/
theorem RegisteredRootTest.liftDeleted_good {r h : ℕ} (D : Finset V)
    (test : RegisteredRootTest ↥(univ \ D) r h)
    (data : SimpleHypergraph V × SimpleHypergraph V) (e : Finset V)
    (he : e ∈ rootEdgeUniverse r test.root.val) :
    e ∉ (test.liftDeleted D).badSet data ↔
      e ⊆ univ \ D ∧ restrictEdge (univ \ D) e ∉
        test.badSet (inducedHost (univ \ D) data.1, inducedHost (univ \ D) data.2) := by
  simp [RegisteredRootTest.liftDeleted, he]

/-- The surviving restriction is an actual root edge of the residual universe. -/
theorem RegisteredRootTest.liftDeleted_good_rootEdge {r h : ℕ} (D : Finset V)
    (test : RegisteredRootTest ↥(univ \ D) r h)
    (data : SimpleHypergraph V × SimpleHypergraph V) (e : Finset V)
    (he : e ∈ rootEdgeUniverse r test.root.val)
    (hg : e ∉ (test.liftDeleted D).badSet data) :
    restrictEdge (univ \ D) e ∈ rootEdgeUniverse r test.root := by
  have hs := ((test.liftDeleted_good D data e he).mp hg).1
  obtain ⟨hc, hx⟩ := (mem_rootEdgeUniverse _ _ _).mp he
  apply (mem_rootEdgeUniverse _ _ _).mpr
  constructor
  · rw [← liftEdge_card, lift_restrictEdge _ _ hs]
    exact hc
  · exact (mem_restrictEdge _ _ _).mpr hx

/-- In particular the good edge is disjoint from the deleted set. -/
theorem RegisteredRootTest.liftDeleted_good_disjoint {r h : ℕ} (D : Finset V)
    (test : RegisteredRootTest ↥(univ \ D) r h)
    (data : SimpleHypergraph V × SimpleHypergraph V) (e : Finset V)
    (he : e ∈ rootEdgeUniverse r test.root.val)
    (hg : e ∉ (test.liftDeleted D).badSet data) : Disjoint e D := by
  have hs := ((test.liftDeleted_good D data e he).mp hg).1
  exact disjoint_left.mpr fun v hv hd => (mem_sdiff.mp (hs hv)).2 hd

/-- Empty prescriptions remain empty when transported to the ambient universe. -/
theorem RegisteredRootTest.liftDeleted_prescribed_empty {r h : ℕ} (D : Finset V)
    (test : RegisteredRootTest ↥(univ \ D) r h) (hp : test.prescribed = ∅) :
    (test.liftDeleted D).prescribed = ∅ := by
  simp [RegisteredRootTest.liftDeleted, hp]

/-- The residual predicate receives root-free induced observations of the same
ambient terminal/current hosts, without a new residual probability law. -/
theorem RegisteredRootTest.liftDeleted_good_rootFree {r h : ℕ} (D : Finset V)
    (test : RegisteredRootTest ↥(univ \ D) r h)
    (terminal current : SimpleHypergraph V) (e : Finset V)
    (he : e ∈ rootEdgeUniverse r test.root.val) :
    e ∉ (test.liftDeleted D).badSet
      (rootFreeEdges test.root.val terminal, rootFreeEdges test.root.val current) ↔
    e ⊆ univ \ D ∧ restrictEdge (univ \ D) e ∉ test.badSet
      (rootFreeEdges test.root (inducedHost (univ \ D) terminal),
       rootFreeEdges test.root (inducedHost (univ \ D) current)) := by
  rw [test.liftDeleted_good D _ e he]
  rw [inducedHost_rootFree_commute (univ \ D) terminal test.root,
    inducedHost_rootFree_commute (univ \ D) current test.root]

/-- Passing the lifted test gives precisely the ambient sampling conclusion.
The degree and deficit assumptions refer to the ambient root-free observation. -/
theorem RegisteredRootTest.liftDeleted_passes {r h M : ℕ} {ell : V → ℕ}
    (D : Finset V) (test : RegisteredRootTest ↥(univ \ D) r h) (c : ℝ)
    (ω : TerminalState V r M ell × MissingOrder V r M)
    (hpass : ¬ (test.liftDeleted D).failure M ell c ω)
    (ht : M ≤ test.time) (hK : test.time ≤ (completeEdges V r).card)
    (hR : (test.liftDeleted D).prescribed ⊆ (rootSamplingPair r M ell test.time ω).2)
    (hdef : (∑ v, rootAdjustedDeficit test.root.val ell
      (rootFreePairObservation r M ell test.time test.root.val ω).1 v) ≤ 1)
    (hdeg : c * FrameScales.L1 (Fintype.card V) ≤
      ((test.time - (rootFreePairObservation r M ell test.time test.root.val ω).2.card : ℕ) : ℝ))
    (hdens : rootLinkDensity r test.root.val ((test.liftDeleted D).badSet
      (rootFreePairObservation r M ell test.time test.root.val ω)) ≤
      FrameScales.rho (Fintype.card V)) :
    ¬ RootLinkBad ((test.liftDeleted D).badSet
      (rootFreePairObservation r M ell test.time test.root.val ω))
      (test.time - (rootFreePairObservation r M ell test.time test.root.val ω).2.card)
      (rootSamplingPair r M ell test.time ω) := by
  intro hbad
  exact hpass ⟨ht,hK,hR,hdef,hdeg,hdens,hbad⟩

end LooseHamilton
