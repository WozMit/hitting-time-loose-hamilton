module

public import HittingTimeLooseHamilton.BootstrapActualTests

public section

/-! Literal coverage of every fixed base/port test and invariance under the
root-free observation map. Eligibility and cut presence are not registration
gates. The endpoint constructors use the actual residual outer-host mean. -/
noncomputable section
namespace LooseHamilton.BootstrapCatalogue
open Finset RootFreeTestIndexing
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Exact equality, not a comparison to an auxiliary test. -/
theorem tests_base {r h : ℕ} {M : Finset (Finset V)} (hM : IsPairMatching M)
    (cP cE cPort : ℝ) (b : BootstrapBases.Base M) (l : BaseLabel r V) (j)
    (hi : admissible (.inl (b,l))) :
    tests (h := h) hM cP cE cPort (baseIndex b l j) =
      (residualTest hM cP cE j.val b l hi.1).liftDeleted (BootstrapBases.deleted b) := by
  rw [tests_valid _ _ _ _ _ hi]
  rfl

theorem tests_port {r h : ℕ} {M : Finset (Finset V)} (hM : IsPairMatching M)
    (cP cE cPort : ℝ) (l : PortLabel r V) (j)
    (hi : portSourceDistinct l) :
    tests (h := h) hM cP cE cPort (portIndex l j) =
      registerPortRootTest r h j.val M (originalPorts M) l.1.val
        l.2.1 l.2.2.1 l.2.2.2 cPort := by
  rw [tests_valid hM cP cE cPort (portIndex l j) hi]
  rfl

/-- Literal ambient bad set, including all deletion collisions. -/
theorem tests_base_badSet {r h : ℕ} {M : Finset (Finset V)} (hM : IsPairMatching M)
    (cP cE cPort : ℝ) (b : BootstrapBases.Base M) (l : BaseLabel r V) (j)
    (hi : admissible (.inl (b,l))) (data : SimpleHypergraph V × SimpleHypergraph V) :
    (tests (h := h) hM cP cE cPort (baseIndex b l j)).badSet data =
      (rootEdgeUniverse r (root (.inl (b,l)))).filter (fun e =>
        ¬ e ⊆ BootstrapBases.active b ∨
        restrictEdge (BootstrapBases.active b) e ∈
          (residualTest (h := h) hM cP cE j.val b l hi.1).badSet
            (inducedHost (BootstrapBases.active b) data.1,
             inducedHost (BootstrapBases.active b) data.2)) := by
  rw [tests_base _ _ _ _ _ _ _ hi]
  simp only [RegisteredRootTest.liftDeleted, residualTest_root]
  rfl

/-- For every label, the actual residual test is already root-free measurable. -/
theorem residualTest_observation {r h : ℕ} {M : Finset (Finset V)}
    (hM : IsPairMatching M) (cP cE : ℝ) (time) (b) (l : BaseLabel r V) (hs)
    (terminal current : SimpleHypergraph ↥(BootstrapBases.active b)) :
    let T := residualTest (h := h) hM cP cE time b l hs
    T.badSet (rootFreeEdges T.root terminal, rootFreeEdges T.root current) =
      T.badSet (terminal,current) := by
  rcases l with ⟨S,x,y,z,t⟩ | (⟨P,y,z,t,a,R⟩ | ⟨P,y,z,t,u,v,a,R,Q⟩)
  · exact registerPrivateRootTest_observation _ _ _ _ _ _ _ _ _ _ _ _
  · exact registerEndpointRootTest_observation _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
  · exact registerEndpointRootTest_observation _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _

/-- The registered lifted test receives precisely the root-free induced hosts. -/
theorem tests_base_observation {r h : ℕ} {M : Finset (Finset V)}
    (hM : IsPairMatching M) (cP cE cPort : ℝ) (b) (l : BaseLabel r V) (j)
    (hi : admissible (.inl (b,l))) (terminal current : SimpleHypergraph V) :
    let T := tests (h := h) hM cP cE cPort (baseIndex b l j)
    T.badSet (rootFreeEdges T.root terminal, rootFreeEdges T.root current) =
      T.badSet (terminal,current) := by
  dsimp only
  rw [tests_base _ _ _ _ _ _ _ hi]
  let T := residualTest (h := h) hM cP cE j.val b l hi.1
  change (rootEdgeUniverse r T.root.val).filter _ = (rootEdgeUniverse r T.root.val).filter _
  have ht := inducedHost_rootFree_commute (BootstrapBases.active b) terminal T.root
  have hc := inducedHost_rootFree_commute (BootstrapBases.active b) current T.root
  have ho := residualTest_observation (h := h) hM cP cE j.val b l hi.1
    (inducedHost (BootstrapBases.active b) terminal)
    (inducedHost (BootstrapBases.active b) current)
  change T.badSet _ = T.badSet _ at ho
  change (rootEdgeUniverse r T.root.val).filter (fun e =>
    ¬ e ⊆ BootstrapBases.active b ∨ restrictEdge (BootstrapBases.active b) e ∈
      T.badSet (inducedHost (BootstrapBases.active b) (rootFreeEdges T.root.val terminal),
        inducedHost (BootstrapBases.active b) (rootFreeEdges T.root.val current))) = _
  rw [ht, hc, ho]
  rfl

/-- Observation equality for all entries, including invalid-label dummies. -/
theorem tests_observation {r h : ℕ} {M : Finset (Finset V)}
    (hM : IsPairMatching M) (cP cE cPort : ℝ) (i : Index r M)
    (terminal current : SimpleHypergraph V) :
    let T := tests (h := h) hM cP cE cPort i
    T.badSet (rootFreeEdges T.root terminal, rootFreeEdges T.root current) =
      T.badSet (terminal,current) := by
  dsimp only
  by_cases hi : admissible i.1
  · rcases i with ⟨⟨b,l⟩ | l,j⟩
    · exact tests_base_observation _ _ _ _ _ _ _ hi _ _
    · rw [show ((Sum.inr l,j) : Index r M) = portIndex l j from rfl,
        tests_port _ _ _ _ _ _ hi]
      exact registerPortRootTest_observation _ _ _ _ _ _ _ _ _ _ _ _
  · rw [tests_invalid _ _ _ _ _ hi]
    rfl

end LooseHamilton.BootstrapCatalogue
