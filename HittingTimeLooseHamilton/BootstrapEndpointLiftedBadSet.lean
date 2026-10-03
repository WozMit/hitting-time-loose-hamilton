module

public import HittingTimeLooseHamilton.BootstrapMobilityConstants
public import HittingTimeLooseHamilton.BootstrapEndpointRegisteredCapture
public import HittingTimeLooseHamilton.BootstrapEndpointLiftedGeometry
public import HittingTimeLooseHamilton.BootstrapEndpointResidualFrames

public section

/-! The literal lifted endpoint test is captured by abnormal candidates of its
actual ambient core, plus the explicit ambient collision family. -/
noncomputable section
namespace LooseHamilton.BootstrapEndpointLiftedBadSet
open Finset BootstrapBases BootstrapEndpointLinkGeometry
variable {V : Type} [Fintype V] [DecidableEq V]
variable {r : ℕ} {M : Finset (Finset V)}
attribute [local instance] Classical.propDecidable

@[expose] def cutMarkers (markers : SimpleHypergraph V) (z : V) : RootFreeEndpointLabel V → SimpleHypergraph V
  | .inl l => l.markers markers z
  | .inr l => l.markers markers z

/-- Literal metadata of the unoriented core; candidate counts will prescribe
both the root start and the relative start. -/
structure CoreShape (hM : IsPairMatching M) (b : Base M)
    (P : Finset ↥(active b)) (y z : ↥(active b))
    (l : RootFreeEndpointLabel ↥(active b)) (F : AuxiliaryFrame.Frame r M) : Prop where
  deleted_eq : F.val.deleted = deleted b ∪ liftEdge (active b) (P ∪ cutDeleted y l)
  markers_eq : F.markers = (cutMarkers (restrictEdges (active b) (markers hM b)) z l).image
    (liftEdge (active b))
  root_eq : F.val.root = ((cutEndpoint l).val,z.val)
  relative_eq : F.val.relative = none

/-- Bad sets do not depend on the prescribed subset; it is kept in the actual
registry for its sampling event. This definition uses the empty representative. -/
@[expose] def registeredBadSet (r h time : ℕ) (hM : IsPairMatching M) (b : Base M)
    (P : Finset ↥(active b)) (y z t : ↥(active b))
    (l : RootFreeEndpointLabel ↥(active b)) (J H : SimpleHypergraph V) : SimpleHypergraph V :=
  ((registerEndpointRootTest r h time (restrictEdges (active b) (markers hM b))
    P (fixedPorts b) y z t l (BootstrapConstants.rootThreshold r) ∅
      (empty_subset _) (by simp)).liftDeleted (deleted b)).badSet (J,H)

theorem registeredBadSet_eq_prescribed (r h time : ℕ) (hM : IsPairMatching M) (b : Base M)
    (P : Finset ↥(active b)) (y z t : ↥(active b))
    (l : RootFreeEndpointLabel ↥(active b)) (J H : SimpleHypergraph V)
    (R : SimpleHypergraph ↥(active b)) (hR : R ⊆ rootEdgeUniverse r y) (hcard : R.card ≤ h) :
    registeredBadSet r h time hM b P y z t l J H =
      ((registerEndpointRootTest r h time (restrictEdges (active b) (markers hM b))
        P (fixedPorts b) y z t l (BootstrapConstants.rootThreshold r) R hR hcard).liftDeleted (deleted b)).badSet (J,H) := rfl

theorem observation_eq (r h time : ℕ) (hM : IsPairMatching M) (b : Base M)
    (P : Finset ↥(active b)) (y z t : ↥(active b))
    (l : RootFreeEndpointLabel ↥(active b)) (J H : SimpleHypergraph V) :
    registeredBadSet r h time hM b P y z t l (rootFreeEdges y.val J) (rootFreeEdges y.val H) =
      registeredBadSet r h time hM b P y z t l J H := by
  have ho := registerEndpointRootTest_observation r h time
    (restrictEdges (active b) (markers hM b)) (inducedHost (active b) J)
    (inducedHost (active b) H) P (fixedPorts b) y z t l (BootstrapConstants.rootThreshold r)
    ∅ (empty_subset _) (by simp : (∅ : SimpleHypergraph ↥(active b)).card ≤ h)
  let test := registerEndpointRootTest r h time
    (restrictEdges (active b) (markers hM b)) P (fixedPorts b) y z t l
    (BootstrapConstants.rootThreshold r) ∅ (empty_subset _) (by simp : (∅ : SimpleHypergraph ↥(active b)).card ≤ h)
  have hd : (inducedHost (active b) (rootFreeEdges y.val J),
      inducedHost (active b) (rootFreeEdges y.val H)) =
      (rootFreeEdges y (inducedHost (active b) J), rootFreeEdges y (inducedHost (active b) H)) :=
    congrArg₂ Prod.mk (inducedHost_rootFree_commute (active b) J y)
      (inducedHost_rootFree_commute (active b) H y)
  have hc := congrArg
    (fun data : SimpleHypergraph ↥(active b) × SimpleHypergraph ↥(active b) =>
      (rootEdgeUniverse r y.val).filter fun e =>
        ¬ e ⊆ active b ∨ restrictEdge (active b) e ∈ test.badSet data)
    hd
  exact hc.trans (congrArg (fun B => (rootEdgeUniverse r y.val).filter fun e =>
    ¬ e ⊆ active b ∨ restrictEdge (active b) e ∈ B) ho)

theorem source_count (hM : IsPairMatching M) (b : Base M)
    (P : Finset ↥(active b)) (y z : ↥(active b)) (l : RootFreeEndpointLabel ↥(active b))
    (F : AuxiliaryFrame.Frame r M) (hshape : CoreShape hM b P y z l F)
    (H : SimpleHypergraph V) (hH : H ⊆ completeEdges V r) :
    F.cycleCount H = rootFreeEndpointX r (restrictEdges (active b) (markers hM b))
      (fixedPortHost (inducedHost (active b) H) (fixedPorts b)) P y z l := by
  cases l with
  | inl l =>
    exact BootstrapEndpointRegisteredCapture.source_I hM b F H hH P y z l
      hshape.deleted_eq hshape.markers_eq hshape.relative_eq
  | inr l =>
    exact BootstrapEndpointRegisteredCapture.source_II hM b F H hH P y z l
      hshape.deleted_eq hshape.markers_eq hshape.relative_eq

/-- The combined structural estimate needs only static target freshness, actual
positive source count and alpha≤1/2; no balance or capture premise is imposed. -/
theorem badSet_subset (h time : ℕ) (hM : IsPairMatching M) (b : Base M)
    (F : AuxiliaryFrame.Frame r M) (hr : 3 ≤ r) (J H : SimpleHypergraph V)
    (hH : H ⊆ completeEdges V r) (P : Finset ↥(active b))
    (y z t : ↥(active b)) (l : RootFreeEndpointLabel ↥(active b))
    (hshape : CoreShape hM b P y z l F)
    (ht : t ∉ P ∪ cutDeleted y l ∪ fixedPorts b ∪ {y,z,cutEndpoint l})
    (hX : 0 < rootFreeEndpointX r (restrictEdges (active b) (markers hM b))
      (fixedPortHost (inducedHost (active b) H) (fixedPorts b)) P y z l)
    (α : ℝ) (hα : α ≤ 1/2) :
    registeredBadSet r h time hM b P y z t l J H ⊆
      (endpointBadCandidateFiber (frameAbnormalCandidates F H α) t.val).image
        (endpointCandidateRootEdge y.val) ∪
      deletedRootCollisions r y.val (BootstrapEndpointLiftedGeometry.exclusions hM b P y z t l) := by
  intro e he
  by_cases hc : e ∈ deletedRootCollisions r y.val
      (BootstrapEndpointLiftedGeometry.exclusions hM b P y z t l)
  · exact mem_union_right _ hc
  have heroot : e ∈ rootEdgeUniverse r y.val := (mem_filter.mp he).1
  have htports : t ∉ fixedPorts b := fun hp => ht (mem_union_left _ (mem_union_right _ hp))
  have htfresh : t ∉ P ∪ cutDeleted y l ∪
      originalPorts (restrictEdges (active b) (markers hM b)) ∪ {y,z,cutEndpoint l} := by
    intro hf
    apply ht
    rcases mem_union.mp hf with hf | hf
    · rcases mem_union.mp hf with hf | hf
      · exact mem_union_left _ (mem_union_left _ hf)
      · exact mem_union_left _ (mem_union_right _ (BootstrapPrivateLinkGeometry.marker_ports_subset hM b hf))
    · exact mem_union_right _ hf
  obtain ⟨hs,ha,q,hq⟩ := BootstrapEndpointLiftedGeometry.surviving_split hM b (by omega)
    (fixedPortHost (inducedHost (active b) H) (fixedPorts b)) P y z t l htfresh e heroot hc
  have htest := ((registerEndpointRootTest r h time (restrictEdges (active b) (markers hM b))
    P (fixedPorts b) y z t l (BootstrapConstants.rootThreshold r) ∅
    (empty_subset _) (by simp)).liftDeleted_surviving (deleted b) (J,H) e heroot hs).mp he
  change restrictEdge (active b) e ∈ (rootEdgeUniverse r y).filter
    (fun a => a ∉ allowedEdges r (fixedPorts b) ∨
      ∀ q, RootFreeEndpointSplit r (restrictEdges (active b) (markers hM b))
        (fixedPortHost (inducedHost (active b) H) (fixedPorts b)) P y z t a l q →
        (rootFreeEndpointY r (restrictEdges (active b) (markers hM b))
          (fixedPortHost (inducedHost (active b) H) (fixedPorts b)) P y z t l q : ℝ) <
          BootstrapConstants.rootThreshold r * rootFreeEndpointX r
            (restrictEdges (active b) (markers hM b))
            (fixedPortHost (inducedHost (active b) H) (fixedPorts b)) P y z l /
            rootFreeEndpointMean r (inducedHost (active b) H) P y l) at htest
  have hbad := (mem_filter.mp htest).2
  have hlow := (hbad.resolve_left (not_not.mpr ha)) q hq
  have hcap : (liftEdge (active b) q.1,q.2.val,t.val) ∈ frameAbnormalCandidates F H α := by
    cases l with
    | inl l =>
      exact BootstrapEndpointRegisteredCapture.low_summand_I hM b F H hH P y z l
        hshape.deleted_eq hshape.markers_eq hr hshape.root_eq hshape.relative_eq _ t q hq.2
        (by rw [hq.1]; exact ha) htports hX α hα hlow
    | inr l =>
      exact BootstrapEndpointRegisteredCapture.low_summand_II hM b F H hH P y z l
        hshape.deleted_eq hshape.markers_eq hr hshape.root_eq hshape.relative_eq _ t q hq.2
        (by rw [hq.1]; exact ha) htports hX α hα hlow
  have hrec : {y,q.2} ∪ q.1 = restrictEdge (active b) e := by cases l <;> exact hq.1
  exact mem_union_left _ (mem_image.mpr ⟨_,mem_filter.mpr ⟨hcap,rfl⟩,
    endpoint_reconstruct_lift (active b) y t q e hs hrec⟩)

end LooseHamilton.BootstrapEndpointLiftedBadSet
