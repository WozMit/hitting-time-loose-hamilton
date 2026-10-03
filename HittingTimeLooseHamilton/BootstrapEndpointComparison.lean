module

public import HittingTimeLooseHamilton.BootstrapEndpointLiftedBadSet

public section

/-! Item 33.16: actual endpoint core frames, exact source dictionaries, and
reconstruction/counting for the literal lifted endpoint test on both bases. -/
noncomputable section
namespace LooseHamilton.BootstrapEndpointComparison
open Finset BootstrapBases BootstrapEndpointLinkGeometry BootstrapEndpointLiftedBadSet
variable {V : Type} [Fintype V] [DecidableEq V]
variable {r : ℕ} {M : Finset (Finset V)}

@[expose] def CutLegal (r : ℕ) (markers G : SimpleHypergraph V) (P : Finset V) (y z : V) :
    RootFreeEndpointLabel V → Prop
  | .inl l => EndpointCutLegalI r markers G P y z l
  | .inr l => EndpointCutLegalII r markers G P y z l

/-- Every legal residual cut on either base has an actual ambient core frame. -/
theorem exists_core (hM : IsPairMatching M) (b : Base M) (hr : 3 ≤ r)
    (G : SimpleHypergraph ↥(active b)) (P : Finset ↥(active b)) (y z : ↥(active b))
    (l : RootFreeEndpointLabel ↥(active b))
    (hs : LegalPrivateCompletion r (restrictEdges (active b) (markers hM b)) P {y,z})
    (hl : CutLegal r (restrictEdges (active b) (markers hM b)) G P y z l) :
    ∃ F : AuxiliaryFrame.Frame r M, CoreShape hM b P y z l F := by
  cases l with
  | inl l =>
    obtain ⟨F,hd,hm,hroot,hrel⟩ := BootstrapEndpointResidualFrames.endpointI_core_exists hM b hr hs hl
    exact ⟨F,hd,hm,hroot,hrel⟩
  | inr l =>
    obtain ⟨F,hd,hm,hroot,hrel⟩ := BootstrapEndpointResidualFrames.endpointII_core_exists hM b hr hs hl
    exact ⟨F,hd,hm,hroot,hrel⟩

theorem cut_deleted_card_le (hr : 3 ≤ r) (markers G : SimpleHypergraph V)
    (P : Finset V) (y z : V) (l : RootFreeEndpointLabel V)
    (hl : CutLegal r markers G P y z l) : (cutDeleted y l).card ≤ 2*(r-2)+3 := by
  cases l with
  | inl l =>
    have hc := cutDeleted_card_I markers G P y z l hl
    omega
  | inr l => exact cutDeleted_card_II markers G P y z l hl

/-- Every noncolliding bad edge injects into actual abnormal directed candidates
with target t. The injection is constructed from exact edge reconstruction. -/
theorem badSet_noncolliding_injection (h time : ℕ) (hM : IsPairMatching M) (b : Base M)
    (F : AuxiliaryFrame.Frame r M) (hr : 3 ≤ r) (J H : SimpleHypergraph V)
    (hH : H ⊆ completeEdges V r) (P : Finset ↥(active b))
    (y z t : ↥(active b)) (l : RootFreeEndpointLabel ↥(active b))
    (hshape : CoreShape hM b P y z l F)
    (ht : t ∉ P ∪ cutDeleted y l ∪ fixedPorts b ∪ {y,z,cutEndpoint l})
    (hX : 0 < rootFreeEndpointX r (restrictEdges (active b) (markers hM b))
      (fixedPortHost (inducedHost (active b) H) (fixedPorts b)) P y z l)
    (α : ℝ) (hα : α ≤ 1/2) :
    ∃ f : ↥(registeredBadSet r h time hM b P y z t l J H \
      deletedRootCollisions r y.val (BootstrapEndpointLiftedGeometry.exclusions hM b P y z t l)) →
      ↥(endpointBadCandidateFiber (frameAbnormalCandidates F H α) t.val),
      Function.Injective f ∧ ∀ e, endpointCandidateRootEdge y.val (f e).val = e.val :=
  exists_endpoint_reconstruction_injection y.val _ _ _
    (badSet_subset h time hM b F hr J H hH P y z t l hshape ht hX α hα)

/-- The error term is fully explicit and uses ambient N, not the residual size. -/
theorem badSet_card_le (h time : ℕ) (hM : IsPairMatching M) (b : Base M)
    (F : AuxiliaryFrame.Frame r M) (hr : 3 ≤ r) (J H : SimpleHypergraph V)
    (hH : H ⊆ completeEdges V r) (P : Finset ↥(active b))
    (y z t : ↥(active b)) (l : RootFreeEndpointLabel ↥(active b))
    (hshape : CoreShape hM b P y z l F)
    (hP : P.card = r-2) (hcut : (cutDeleted y l).card ≤ 2*(r-2)+3)
    (ht : t ∉ P ∪ cutDeleted y l ∪ fixedPorts b ∪ {y,z,cutEndpoint l})
    (hX : 0 < rootFreeEndpointX r (restrictEdges (active b) (markers hM b))
      (fixedPortHost (inducedHost (active b) H) (fixedPorts b)) P y z l)
    (α : ℝ) (hα : α ≤ 1/2) :
    (registeredBadSet r h time hM b P y z t l J H).card ≤
      (endpointBadCandidateFiber (frameAbnormalCandidates F H α) t.val).card +
        (2*M.card+3*r+2)*(Fintype.card V-2).choose (r-2) := by
  have hs := badSet_subset h time hM b F hr J H hH P y z t l hshape ht hX α hα
  have hc : (registeredBadSet r h time hM b P y z t l J H).card ≤
      (endpointBadCandidateFiber (frameAbnormalCandidates F H α) t.val).card +
      (deletedRootCollisions r y.val (BootstrapEndpointLiftedGeometry.exclusions hM b P y z t l)).card :=
    (card_le_card hs).trans ((card_union_le _ _).trans (Nat.add_le_add_right card_image_le _))
  exact hc.trans (Nat.add_le_add_left
    (BootstrapEndpointLiftedGeometry.collisions_card_le hM hr b P y z t l hP hcut) _)

/-- Final frame-to-test comparison. Choose the core from legal labels, before
H or target selection. Count capture and structural bounds are conclusions;
candidate balance and averaging are the subsequent item 33.17. -/
theorem exists_core_comparison (hM : IsPairMatching M) (b : Base M) (hr : 3 ≤ r)
    (G : SimpleHypergraph ↥(active b)) (P : Finset ↥(active b)) (y z : ↥(active b))
    (l : RootFreeEndpointLabel ↥(active b))
    (hs : LegalPrivateCompletion r (restrictEdges (active b) (markers hM b)) P {y,z})
    (hl : CutLegal r (restrictEdges (active b) (markers hM b)) G P y z l) :
    ∃ F : AuxiliaryFrame.Frame r M, CoreShape hM b P y z l F ∧
      ∀ (H : SimpleHypergraph V), H ⊆ completeEdges V r →
      F.cycleCount H = rootFreeEndpointX r (restrictEdges (active b) (markers hM b))
        (fixedPortHost (inducedHost (active b) H) (fixedPorts b)) P y z l ∧
      ∀ (h time : ℕ) (J : SimpleHypergraph V) (t : ↥(active b)),
      t ∉ P ∪ cutDeleted y l ∪ fixedPorts b ∪ {y,z,cutEndpoint l} →
      0 < rootFreeEndpointX r (restrictEdges (active b) (markers hM b))
        (fixedPortHost (inducedHost (active b) H) (fixedPorts b)) P y z l →
      ∀ α : ℝ, α ≤ 1/2 →
        (∃ f : ↥(registeredBadSet r h time hM b P y z t l J H \
          deletedRootCollisions r y.val (BootstrapEndpointLiftedGeometry.exclusions hM b P y z t l)) →
          ↥(endpointBadCandidateFiber (frameAbnormalCandidates F H α) t.val),
          Function.Injective f ∧ ∀ e, endpointCandidateRootEdge y.val (f e).val = e.val) ∧
        (registeredBadSet r h time hM b P y z t l J H).card ≤
          (endpointBadCandidateFiber (frameAbnormalCandidates F H α) t.val).card +
            (2*M.card+3*r+2)*(Fintype.card V-2).choose (r-2) := by
  obtain ⟨F,hshape⟩ := exists_core hM b hr G P y z l hs hl
  refine ⟨F,hshape,?_⟩
  intro H hH
  refine ⟨source_count hM b P y z l F hshape H hH,?_⟩
  intro h time J t ht hX α hα
  exact ⟨badSet_noncolliding_injection h time hM b F hr J H hH P y z t l hshape ht hX α hα,
    badSet_card_le h time hM b F hr J H hH P y z t l hshape hs.private_card
      (cut_deleted_card_le hr _ G P y z l hl) ht hX α hα⟩

end LooseHamilton.BootstrapEndpointComparison
