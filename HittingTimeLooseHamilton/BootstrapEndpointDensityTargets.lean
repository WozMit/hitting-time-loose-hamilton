module

public import HittingTimeLooseHamilton.BootstrapEndpointAbnormalFibers
public import HittingTimeLooseHamilton.BootstrapEndpointComparison
public import HittingTimeLooseHamilton.BootstrapAmbientDensityNormalization

public section

/-! Deterministic endpoint density outside one ambient exceptional target set.
The static exclusions guarantee freshness and survival on either base. -/
noncomputable section
namespace LooseHamilton.BootstrapEndpointDensityTargets
open Finset BootstrapBases BootstrapEndpointLinkGeometry BootstrapEndpointLiftedBadSet
variable {V : Type} [Fintype V] [DecidableEq V]
variable {r : ℕ} {M : Finset (Finset V)}

@[expose] def staticTargets (b : Base M) (P : Finset ↥(active b)) (y z : ↥(active b))
    (l : RootFreeEndpointLabel ↥(active b)) : Finset V :=
  deleted b ∪ liftEdge (active b) (P ∪ cutDeleted y l ∪ fixedPorts b ∪ {y,z,cutEndpoint l})

theorem static_card_le (hM : IsPairMatching M) (hr : 3 ≤ r) (b : Base M)
    (P : Finset ↥(active b)) (y z : ↥(active b)) (l : RootFreeEndpointLabel ↥(active b))
    (hP : P.card = r-2) (hcut : (cutDeleted y l).card ≤ 2*(r-2)+3) :
    (staticTargets b P y z l).card ≤ 2*M.card+3*r+2 := by
  have h0 := card_union_le (deleted b)
    (liftEdge (active b) (P ∪ cutDeleted y l ∪ fixedPorts b ∪ {y,z,cutEndpoint l}))
  have h1 := card_union_le (P ∪ cutDeleted y l ∪ fixedPorts b) ({y,z,cutEndpoint l})
  have h2 := card_union_le (P ∪ cutDeleted y l) (fixedPorts b)
  have h3 := card_union_le P (cutDeleted y l)
  have h4 : ({y,z,cutEndpoint l} : Finset ↥(active b)).card ≤ 3 := by
    exact (card_insert_le _ _).trans (Nat.add_le_add_right ((card_insert_le _ _).trans (by simp)) 1)
  have hd := deleted_card_le b
  have hp := BootstrapEndpointLiftedGeometry.fixedPorts_card_le hM b
  simp only [liftEdge_card] at h0
  unfold staticTargets
  omega

@[expose] def excludedTargets (b : Base M) (F : AuxiliaryFrame.Frame r M) (H : SimpleHypergraph V)
    (P : Finset ↥(active b)) (y z : ↥(active b)) (l : RootFreeEndpointLabel ↥(active b))
    (α : ℝ) : Finset V :=
  BootstrapEndpointAbnormalFibers.exceptionalTargets F H α ∪ staticTargets b P y z l

theorem deleted_subset_excluded (b : Base M) (F : AuxiliaryFrame.Frame r M)
    (H : SimpleHypergraph V) (P : Finset ↥(active b)) (y z : ↥(active b))
    (l : RootFreeEndpointLabel ↥(active b)) (α : ℝ) :
    deleted b ⊆ excludedTargets b F H P y z l α := by
  intro v hv
  exact mem_union_right _ (mem_union_left _ hv)

theorem fresh_of_not_excluded (b : Base M) (F : AuxiliaryFrame.Frame r M)
    (H : SimpleHypergraph V) (P : Finset ↥(active b)) (y z t : ↥(active b))
    (l : RootFreeEndpointLabel ↥(active b)) (α : ℝ)
    (ht : t.val ∉ excludedTargets b F H P y z l α) :
    t ∉ P ∪ cutDeleted y l ∪ fixedPorts b ∪ {y,z,cutEndpoint l} := by
  intro hf
  exact ht (mem_union_right _ (mem_union_right _ (mem_image_of_mem _ hf)))

theorem excluded_card_le (hM : IsPairMatching M) (hr : 3 ≤ r) (b : Base M)
    (F : AuxiliaryFrame.Frame r M) (H : SimpleHypergraph V)
    (P : Finset ↥(active b)) (y z : ↥(active b)) (l : RootFreeEndpointLabel ↥(active b))
    (hP : P.card = r-2) (hcut : (cutDeleted y l).card ≤ 2*(r-2)+3)
    (α : ℝ) (hα : 0 < α) (hbalance : ¬ F.candidateBad H α) (hN : 0 < Fintype.card V) :
    ((excludedTargets b F H P y z l α).card : ℝ) ≤
      Real.sqrt α*(Fintype.card V : ℝ) + (2*M.card+3*r+2 : ℕ) := by
  apply BootstrapAmbientDensityNormalization.excluded_union_card_le
  · exact BootstrapEndpointAbnormalFibers.exceptional_card_le hr F H α hα hbalance hN
  · exact_mod_cast static_card_le hM hr b P y z l hP hcut

theorem density_of_not_excluded (h time : ℕ) (hM : IsPairMatching M) (b : Base M)
    (F : AuxiliaryFrame.Frame r M) (hr : 3 ≤ r) (J H : SimpleHypergraph V)
    (hH : H ⊆ completeEdges V r) (P : Finset ↥(active b))
    (y z t : ↥(active b)) (l : RootFreeEndpointLabel ↥(active b))
    (hshape : CoreShape hM b P y z l F)
    (hP : P.card = r-2) (hcut : (cutDeleted y l).card ≤ 2*(r-2)+3)
    (hX : 0 < rootFreeEndpointX r (restrictEdges (active b) (markers hM b))
      (fixedPortHost (inducedHost (active b) H) (fixedPorts b)) P y z l)
    (α : ℝ) (hα : α ≤ 1/2) (hN : 2*r ≤ Fintype.card V)
    (ht : t.val ∉ excludedTargets b F H P y z l α) :
    rootLinkDensity r y.val (registeredBadSet r h time hM b P y z t l
      (rootFreeEdges y.val J) (rootFreeEdges y.val H)) ≤
      ((2:ℝ)^(r-1)*((r-1).factorial:ℝ))*Real.sqrt α +
        (2*M.card+3*r+2 : ℕ)*(r-1 : ℕ)/(Fintype.card V-1 : ℕ) := by
  rw [observation_eq]
  apply BootstrapAmbientDensityNormalization.density_le hr hN y.val _ (Real.sqrt α) _ (Real.sqrt_nonneg _)
  have hc := BootstrapEndpointComparison.badSet_card_le h time hM b F hr J H hH P y z t l
    hshape hP hcut (fresh_of_not_excluded b F H P y z t l α ht) hX α hα
  have hcR : ((registeredBadSet r h time hM b P y z t l J H).card : ℝ) ≤
      ((endpointBadCandidateFiber (frameAbnormalCandidates F H α) t.val).card : ℝ) +
        (2*M.card+3*r+2 : ℕ)*((Fintype.card V-2).choose (r-2) : ℝ) := by exact_mod_cast hc
  exact hcR.trans (add_le_add_left (BootstrapEndpointAbnormalFibers.fiber_card_le_of_not_exceptional
    F H α t.val (fun he => ht (mem_union_left _ he))) _)

/-- The exceptional set is chosen once, independently of the target, the
observed first host and the registry time. Both endpoint cut types are covered. -/
theorem exists_density_targets (hM : IsPairMatching M) (b : Base M)
    (F : AuxiliaryFrame.Frame r M) (hr : 3 ≤ r) (H : SimpleHypergraph V)
    (hH : H ⊆ completeEdges V r) (P : Finset ↥(active b))
    (y z : ↥(active b)) (l : RootFreeEndpointLabel ↥(active b))
    (hshape : CoreShape hM b P y z l F)
    (hP : P.card = r-2) (hcut : (cutDeleted y l).card ≤ 2*(r-2)+3)
    (hX : 0 < rootFreeEndpointX r (restrictEdges (active b) (markers hM b))
      (fixedPortHost (inducedHost (active b) H) (fixedPorts b)) P y z l)
    (α : ℝ) (hαpos : 0 < α) (hα : α ≤ 1/2) (hN : 2*r ≤ Fintype.card V)
    (hbalance : ¬ F.candidateBad H α) :
    ∃ E : Finset V, deleted b ⊆ E ∧
      (E.card : ℝ) ≤ Real.sqrt α*(Fintype.card V : ℝ) + (2*M.card+3*r+2 : ℕ) ∧
      ∀ t : ↥(active b), t.val ∉ E →
        t ∉ P ∪ cutDeleted y l ∪ fixedPorts b ∪ {y,z,cutEndpoint l} ∧
        ∀ (h time : ℕ) (J : SimpleHypergraph V),
          rootLinkDensity r y.val (registeredBadSet r h time hM b P y z t l
            (rootFreeEdges y.val J) (rootFreeEdges y.val H)) ≤
            ((2:ℝ)^(r-1)*((r-1).factorial:ℝ))*Real.sqrt α +
              (2*M.card+3*r+2 : ℕ)*(r-1 : ℕ)/(Fintype.card V-1 : ℕ) := by
  refine ⟨excludedTargets b F H P y z l α, deleted_subset_excluded b F H P y z l α,
    excluded_card_le hM hr b F H P y z l hP hcut α hαpos hbalance (by omega), ?_⟩
  intro t ht
  refine ⟨fresh_of_not_excluded b F H P y z t l α ht, ?_⟩
  intro h time J
  exact density_of_not_excluded h time hM b F hr J H hH P y z t l hshape hP hcut hX α hα hN ht

end LooseHamilton.BootstrapEndpointDensityTargets
