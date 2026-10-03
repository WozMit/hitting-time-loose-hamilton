module

public import HittingTimeLooseHamilton.RootTestRegistry
public import HittingTimeLooseHamilton.RootFreePrivateTests
public import HittingTimeLooseHamilton.RootFreeEndpointMean
public import HittingTimeLooseHamilton.RootFreePortTests
public import HittingTimeLooseHamilton.PathRegularityModels

public section

/-! Concrete registrations of the three manuscript root-link tests. Labels,
ports, constants and time are fixed before observations. The allowed host is
filtered using the fixed original ports, not the changing marker matching. -/
noncomputable section
namespace LooseHamilton
open Finset
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Register the private-coordinate test on full root edges. -/
@[expose] def registerPrivateRootTest (r h time : ℕ) (markers : Finset (Finset V))
    (S q U : Finset V) (x t : V) (c : ℝ) : RegisteredRootTest V r h where
  time := time
  root := x
  prescribed := ∅
  prescribed_subset := empty_subset _
  prescribed_card := by simp
  badSet := fun data => (rootEdgeUniverse r x).filter fun e =>
    PrivateRootBad r markers (allowedEdges r U) (fixedPortHost data.2 U) data.2
      S q x t c (e.erase x)
  bad_subset := fun _ => filter_subset _ _

/-- Register a labelled endpoint-cut test with a bounded prescribed root set.
Prescriptions are fixed labels; the eventual probability theorem includes their
presence as an event rather than conditioning on a selected cut. -/
@[expose] def registerEndpointRootTest (r h time : ℕ) (markers : Finset (Finset V))
    (P U : Finset V) (y z t : V) (l : RootFreeEndpointLabel V) (c : ℝ)
    (R : Finset (Finset V)) (hR : R ⊆ rootEdgeUniverse r y) (hcard : R.card ≤ h) :
    RegisteredRootTest V r h where
  time := time
  root := y
  prescribed := R
  prescribed_subset := hR
  prescribed_card := hcard
  badSet := fun data => rootFreeEndpointBadSet r markers (fixedPortHost data.2 U)
    P U y z t l c (rootFreeEndpointMean r data.2 P y l)
  bad_subset := by
    intro data
    exact filter_subset _ _

/-- Register the original-marker test with the port deleted in every count. -/
@[expose] def registerPortRootTest (r h time : ℕ) (markers : Finset (Finset V))
    (U P : Finset V) (y z u : V) (c : ℝ) : RegisteredRootTest V r h where
  time := time
  root := y
  prescribed := ∅
  prescribed_subset := empty_subset _
  prescribed_card := by simp
  badSet := fun data => (rootEdgeUniverse r y).filter fun e =>
    ¬ (LegalPrivateCompletion r (markers.erase {y,z}) P {u,z} ∧
      y ∉ P ∪ {u,z} ∧ {y,z} ∈ markers ∧ y ≠ z) ∨
    e ∈ rootFreePortBadSet r markers (fixedPortHost data.2 U) U P y z u c
  bad_subset := fun _ => filter_subset _ _

/-- Lift a test on surviving vertices to the original sampling space. Edges
meeting deleted vertices are included among bad edges; surviving edges use the
registered residual test on the induced root-free observations. This introduces
no new conditioning on the residual graph. -/
@[expose] def RegisteredRootTest.liftDeleted {r h : ℕ} (D : Finset V)
    (test : RegisteredRootTest ↥(univ \ D) r h) : RegisteredRootTest V r h where
  time := test.time
  root := test.root.val
  prescribed := test.prescribed.image (liftEdge (univ \ D))
  prescribed_subset := by
    intro e he
    obtain ⟨a,ha,rfl⟩ := mem_image.mp he
    obtain ⟨hac,har⟩ := (mem_rootEdgeUniverse _ _ _).mp (test.prescribed_subset ha)
    apply (mem_rootEdgeUniverse _ _ _).mpr
    constructor
    · simpa using hac
    · exact mem_image.mpr ⟨test.root, har, rfl⟩
  prescribed_card := (card_image_le).trans test.prescribed_card
  badSet := fun data => (rootEdgeUniverse r test.root.val).filter fun e =>
    ¬ e ⊆ univ \ D ∨
      restrictEdge (univ \ D) e ∈
        test.badSet (inducedHost (univ \ D) data.1, inducedHost (univ \ D) data.2)
  bad_subset := fun _ => filter_subset _ _

/-- The lift explicitly rejects every root edge colliding with the deletion. -/
theorem RegisteredRootTest.liftDeleted_collision {r h : ℕ} (D : Finset V)
    (test : RegisteredRootTest ↥(univ \ D) r h)
    (data : SimpleHypergraph V × SimpleHypergraph V) (e : Finset V)
    (he : e ∈ rootEdgeUniverse r test.root.val) (hD : ¬ e ⊆ univ \ D) :
    e ∈ (test.liftDeleted D).badSet data := by
  exact mem_filter.mpr ⟨he, Or.inl hD⟩

/-- For a surviving edge, lifted badness is exactly residual badness. -/
theorem RegisteredRootTest.liftDeleted_surviving {r h : ℕ} (D : Finset V)
    (test : RegisteredRootTest ↥(univ \ D) r h)
    (data : SimpleHypergraph V × SimpleHypergraph V) (e : Finset V)
    (he : e ∈ rootEdgeUniverse r test.root.val) (hD : e ⊆ univ \ D) :
    e ∈ (test.liftDeleted D).badSet data ↔
      restrictEdge (univ \ D) e ∈
        test.badSet (inducedHost (univ \ D) data.1, inducedHost (univ \ D) data.2) := by
  simp only [RegisteredRootTest.liftDeleted, mem_filter, he, true_and, hD, not_true_eq_false,
    false_or]


/-- Restricting the two observed hosts commutes with withholding the root link.
Thus the residual test receives exactly its own root-free observations. -/
theorem inducedHost_rootFree_commute (S : Finset V) (host : SimpleHypergraph V)
    (x : ↥S) :
    inducedHost S (rootFreeEdges x.val host) = rootFreeEdges x (inducedHost S host) := by
  ext e
  have hroot : x.val ∈ ambientEdge S e ↔ x ∈ e := by
    simp [ambientEdge]
  simp only [mem_inducedHost, rootFreeEdges, mem_filter, hroot]


/-- The fixed original-port filter commutes with withholding a root link. -/
theorem fixedPortHost_rootFreeEdges (host : SimpleHypergraph V) (U : Finset V) (x : V) :
    fixedPortHost (rootFreeEdges x host) U = rootFreeEdges x (fixedPortHost host U) := by
  ext e
  simp [fixedPortHost, rootFreeEdges, and_left_comm, and_comm, and_assoc]

/-- Evaluating the registered private test from the observed root-free pair
agrees with its literal actual-host definition. -/
theorem registerPrivateRootTest_observation (r h time : ℕ)
    (markers terminal current : SimpleHypergraph V) (S q U : Finset V)
    (x t : V) (c : ℝ) :
    (registerPrivateRootTest r h time markers S q U x t c).badSet
        (rootFreeEdges x terminal, rootFreeEdges x current) =
      (registerPrivateRootTest r h time markers S q U x t c).badSet (terminal,current) := by
  ext e
  simp only [registerPrivateRootTest, mem_filter, fixedPortHost_rootFreeEdges,
    privateRootBad_rootFreeEdges]


/-- The endpoint registration computes its literal actual-host test, including
its actual root-free outer-host mean. -/
theorem registerEndpointRootTest_observation (r h time : ℕ)
    (markers terminal current : SimpleHypergraph V) (P U : Finset V)
    (y z t : V) (l : RootFreeEndpointLabel V) (c : ℝ)
    (R : SimpleHypergraph V) (hR : R ⊆ rootEdgeUniverse r y) (hcard : R.card ≤ h) :
    (registerEndpointRootTest r h time markers P U y z t l c R hR hcard).badSet
        (rootFreeEdges y terminal, rootFreeEdges y current) =
      (registerEndpointRootTest r h time markers P U y z t l c R hR hcard).badSet
        (terminal,current) := by
  dsimp only [registerEndpointRootTest]
  apply rootFreeEndpointBadSet_mean_congr
  · rw [fixedPortHost_rootFreeEdges, rootFreeEdges_idempotent]
  · exact rootFreeEdges_idempotent _ _

/-- The port registration agrees with the literal deleted-port test. Its
source-validity gate consists only of fixed labels and is unchanged. -/
theorem registerPortRootTest_observation (r h time : ℕ)
    (markers terminal current : SimpleHypergraph V) (U P : Finset V)
    (y z u : V) (c : ℝ) :
    (registerPortRootTest r h time markers U P y z u c).badSet
        (rootFreeEdges y terminal, rootFreeEdges y current) =
      (registerPortRootTest r h time markers U P y z u c).badSet (terminal,current) := by
  have he := rootFreePortBadSet_congr r markers
    (fixedPortHost (rootFreeEdges y current) U) (fixedPortHost current U) U P y z u c
    (by rw [fixedPortHost_rootFreeEdges, rootFreeEdges_idempotent])
  ext e
  simp only [registerPortRootTest, mem_filter, he]

end LooseHamilton
