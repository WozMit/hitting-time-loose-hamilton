module

public import HittingTimeLooseHamilton.BootstrapPrivateLiftedDensity

public section

/-! Ambient exceptional targets for the literal lifted private test. The
static exclusions include the base deletion, so every remaining ambient target
belongs to the residual base. -/
noncomputable section
namespace LooseHamilton.BootstrapPrivateDensityTargets
open Finset BootstrapBases BootstrapPrivateLinkGeometry BootstrapPrivateLiftedBadSet
variable {V : Type} [Fintype V] [DecidableEq V]
variable {r : ℕ} {M : Finset (Finset V)}

@[expose] def excludedTargets (b : Base M) (F : AuxiliaryFrame.Frame r M)
    (H : SimpleHypergraph V) (S q : Finset ↥(active b)) (x : ↥(active b)) (α : ℝ) : Finset V :=
  BootstrapPrivateAbnormalFibers.exceptionalTargets F H α ∪ exclusions b S q x

theorem deleted_subset_excluded (b : Base M) (F : AuxiliaryFrame.Frame r M)
    (H : SimpleHypergraph V) (S q : Finset ↥(active b)) (x : ↥(active b)) (α : ℝ) :
    deleted b ⊆ excludedTargets b F H S q x α := by
  intro v hv
  apply mem_union_right
  simp only [exclusions,mem_union,mem_singleton]
  tauto

theorem outside_excluded_survives (b : Base M) (F : AuxiliaryFrame.Frame r M)
    (H : SimpleHypergraph V) (S q : Finset ↥(active b)) (x : ↥(active b)) (α : ℝ)
    (t : V) (ht : t ∉ excludedTargets b F H S q x α) : t ∈ active b :=
  mem_sdiff.mpr ⟨mem_univ _,fun h => ht (deleted_subset_excluded b F H S q x α h)⟩

theorem excluded_card_le (hM : IsPairMatching M) (hr : 3 ≤ r) (b : Base M)
    (F : AuxiliaryFrame.Frame r M) (H : SimpleHypergraph V)
    (S q : Finset ↥(active b)) (x : ↥(active b))
    (hS : S.card = r-3) (hq : q.card = 2)
    (α : ℝ) (hα : 0 < α) (hbalance : ¬ F.candidateBad H α) (hN : 0 < Fintype.card V) :
    ((excludedTargets b F H S q x α).card : ℝ) ≤
      Real.sqrt ((r-2 : ℕ)*α)*(Fintype.card V : ℝ) + (2*M.card+r+1 : ℕ) := by
  apply BootstrapAmbientDensityNormalization.excluded_union_card_le
  · exact BootstrapPrivateAbnormalFibers.exceptional_card_le hr F H α hα hbalance hN
  · exact_mod_cast exclusions_card_le hM hr b S q x hS hq

theorem density_of_not_excluded (h time : ℕ) (hM : IsPairMatching M) (b : Base M)
    (F : AuxiliaryFrame.Frame r M) (hr : 3 ≤ r) (J H : SimpleHypergraph V)
    (hH : H ⊆ completeEdges V r) (S q : Finset ↥(active b)) (x t : ↥(active b))
    (hS : S.card = r-3)
    (hs : LegalPrivateCompletion r (restrictEdges (active b) (markers hM b)) (insert x S) q)
    (hd : F.val.deleted = deleted b ∪ liftEdge (active b) (insert x S))
    (hm : F.markers = insert (liftEdge (active b) q) (markers hM b))
    (hrel : F.val.relative = none)
    (hW : 0 < completionCount r (restrictEdges (active b) (markers hM b))
      (fixedPortHost (inducedHost (active b) H) (fixedPorts b)) (insert x S) q)
    (α : ℝ) (hα : α ≤ 1/2) (hN : 2*r ≤ Fintype.card V)
    (ht : t.val ∉ excludedTargets b F H S q x α) :
    rootLinkDensity r x.val (registeredBadSet r h time hM b S q x t
      (rootFreeEdges x.val J) (rootFreeEdges x.val H)) ≤
      ((2:ℝ)^(r-1)*((r-1).factorial:ℝ))*Real.sqrt ((r-2 : ℕ)*α) +
        (2*M.card+r+1 : ℕ)*(r-1 : ℕ)/(Fintype.card V-1 : ℕ) := by
  have htgeom : t.val ∉ exclusions b S q x := fun ht' => ht (mem_union_right _ ht')
  have htfiber : t.val ∉ BootstrapPrivateAbnormalFibers.exceptionalTargets F H α :=
    fun ht' => ht (mem_union_left _ ht')
  exact BootstrapPrivateLiftedDensity.observed_badSet_density_le h time hM b F hr J H hH
    S q x t hS hs hd hm hrel htgeom hW α hα hN _ (Real.sqrt_nonneg _)
      (BootstrapPrivateAbnormalFibers.fiber_card_le_of_not_exceptional F H α t.val htfiber)

/-- One ambient exceptional set simultaneously controls every eligible lifted
test at its root-free observation. No density or collision bound is a premise. -/
theorem exists_density_targets (h time : ℕ) (hM : IsPairMatching M) (b : Base M)
    (F : AuxiliaryFrame.Frame r M) (hr : 3 ≤ r) (J H : SimpleHypergraph V)
    (hH : H ⊆ completeEdges V r) (S q : Finset ↥(active b)) (x : ↥(active b))
    (hS : S.card = r-3)
    (hs : LegalPrivateCompletion r (restrictEdges (active b) (markers hM b)) (insert x S) q)
    (hd : F.val.deleted = deleted b ∪ liftEdge (active b) (insert x S))
    (hm : F.markers = insert (liftEdge (active b) q) (markers hM b))
    (hrel : F.val.relative = none)
    (hW : 0 < completionCount r (restrictEdges (active b) (markers hM b))
      (fixedPortHost (inducedHost (active b) H) (fixedPorts b)) (insert x S) q)
    (α : ℝ) (hαpos : 0 < α) (hα : α ≤ 1/2) (hN : 2*r ≤ Fintype.card V)
    (hbalance : ¬ F.candidateBad H α) :
    ∃ E : Finset V, deleted b ⊆ E ∧
      (E.card : ℝ) ≤ Real.sqrt ((r-2 : ℕ)*α)*(Fintype.card V : ℝ) + (2*M.card+r+1 : ℕ) ∧
      ∀ t : ↥(active b), t.val ∉ E →
        rootLinkDensity r x.val (registeredBadSet r h time hM b S q x t
          (rootFreeEdges x.val J) (rootFreeEdges x.val H)) ≤
          ((2:ℝ)^(r-1)*((r-1).factorial:ℝ))*Real.sqrt ((r-2 : ℕ)*α) +
            (2*M.card+r+1 : ℕ)*(r-1 : ℕ)/(Fintype.card V-1 : ℕ) := by
  refine ⟨excludedTargets b F H S q x α, deleted_subset_excluded b F H S q x α,
    excluded_card_le hM hr b F H S q x hS hs.pair_card α hαpos hbalance (by omega), ?_⟩
  intro t ht
  exact density_of_not_excluded h time hM b F hr J H hH S q x t hS hs hd hm hrel hW α hα hN ht

end LooseHamilton.BootstrapPrivateDensityTargets
