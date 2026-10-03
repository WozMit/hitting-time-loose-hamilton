module

public import HittingTimeLooseHamilton.BootstrapPrivateLowCapture
public import HittingTimeLooseHamilton.BootstrapNestedMeans

public section

/-! Item 33.16: favorable endpoint normalization and low-count capture. -/
noncomputable section
namespace LooseHamilton.BootstrapEndpointLowCapture
open Finset BootstrapBases BootstrapMeans
variable {V : Type} [Fintype V] [DecidableEq V]
variable {r : ℕ} {M : Finset (Finset V)}
attribute [local instance] Classical.propDecidable

/-- Both cut types have the same ambient surviving set after flattening the base. -/
theorem frame_active_eq (b : Base M) (F : AuxiliaryFrame.Frame r M)
    (P : Finset ↥(active b)) (y : ↥(active b))
    (l : RootFreeEndpointLabel ↥(active b))
    (hd : F.val.deleted = deleted b ∪ liftEdge (active b)
      (match l with | .inl a => P ∪ a.deleted y | .inr a => P ∪ a.deleted y)) :
    F.active = ambientEdge (active b) (rootFreeEndpointActive P y l) := by
  cases l <;> rw [rootFreeEndpointActive,
    BootstrapPrivateSourceNormalization.base_source_active] <;>
    exact congrArg (fun D => univ \ D) hd

/-- The filtered frame mean never exceeds the actual outer endpoint mean. -/
theorem frame_mu_le_outer (b : Base M) (F : AuxiliaryFrame.Frame r M)
    (H : SimpleHypergraph V) (P : Finset ↥(active b)) (y : ↥(active b))
    (l : RootFreeEndpointLabel ↥(active b))
    (hd : F.val.deleted = deleted b ∪ liftEdge (active b)
      (match l with | .inl a => P ∪ a.deleted y | .inr a => P ∪ a.deleted y)) :
    F.mu H ≤ rootFreeEndpointMean r (inducedHost (active b) H) P y l := by
  rw [rootFreeEndpointMean_ambient, ← frame_active_eq b F P y l hd]
  exact F.mu_le_outer_inducedMean H

/-- Positivity is supplied by a nonempty actual source, with no budget premise. -/
theorem positive_normalization (b : Base M) (F : AuxiliaryFrame.Frame r M)
    (hr : 3 ≤ r) (H : SimpleHypergraph V) (P : Finset ↥(active b))
    (y : ↥(active b)) (l : RootFreeEndpointLabel ↥(active b))
    (hd : F.val.deleted = deleted b ∪ liftEdge (active b)
      (match l with | .inl a => P ∪ a.deleted y | .inr a => P ∪ a.deleted y))
    (hX : 0 < F.cycleCount H) :
    0 < F.mu H ∧ F.mu H ≤ rootFreeEndpointMean r (inducedHost (active b) H) P y l ∧
      0 < rootFreeEndpointMean r (inducedHost (active b) H) P y l := by
  have hp := F.mu_pos_of_cycleCount_pos hr H hX
  have hl := frame_mu_le_outer b F H P y l hd
  exact ⟨hp, hl, hp.trans_le hl⟩

/-- Numerical capture at the fixed registry coefficient, retaining the actual
frame completion count and its two prescribed directions. -/
theorem low_count_is_abnormal (b : Base M) (F : AuxiliaryFrame.Frame r M)
    (hr : 3 ≤ r) (H : SimpleHypergraph V) (P : Finset ↥(active b))
    (y : ↥(active b)) (l : RootFreeEndpointLabel ↥(active b))
    (hd : F.val.deleted = deleted b ∪ liftEdge (active b)
      (match l with | .inl a => P ∪ a.deleted y | .inr a => P ∪ a.deleted y))
    (a : Finset V × V × V) (ha : F.LegalCandidate a)
    (hX : 0 < F.cycleCount H) (α : ℝ) (hα : α ≤ 1/2)
    (hlow : (F.completionCount H a : ℝ) <
      (1 / (2 * ((r:ℝ)-1)^2)) * (F.cycleCount H:ℝ) /
        rootFreeEndpointMean r (inducedHost (active b) H) P y l) :
    a ∈ frameAbnormalCandidates F H α := by
  obtain ⟨hμ,hmean,hμraw⟩ := positive_normalization b F hr H P y l hd hX
  have hXreal : (0:ℝ) < F.cycleCount H := by exact_mod_cast hX
  apply mem_filter.mpr
  refine ⟨mem_filter.mpr ⟨mem_univ _,ha⟩,?_⟩
  by_contra hn
  have hbal : |(F.completionCount H a : ℝ) /
      ((F.cycleCount H:ℝ) / (((r:ℝ)-1)^2 * F.mu H)) - 1| ≤ α := le_of_not_gt hn
  have hlower := Migration.balanced_directed_count_lower hr hXreal hμ hbal
  have hcoef : 0 ≤ (1-α)/((r:ℝ)-1)^2 :=
    Migration.candidate_lower_coefficient_nonneg (by linarith)
  have hthreshold : (1 / (2 * ((r:ℝ)-1)^2)) * (F.cycleCount H:ℝ) /
      rootFreeEndpointMean r (inducedHost (active b) H) P y l ≤
      ((1-α)/((r:ℝ)-1)^2) * (F.cycleCount H:ℝ) / F.mu H := by
    calc
      _ ≤ ((1-α)/((r:ℝ)-1)^2) * (F.cycleCount H:ℝ) /
          rootFreeEndpointMean r (inducedHost (active b) H) P y l :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right
            (BootstrapPrivateLowCapture.threshold_le_balance α hα) hXreal.le) hμraw.le
      _ ≤ _ := div_le_div_of_nonneg_left (mul_nonneg hcoef hXreal.le) hμ hmean
  exact (not_lt_of_ge (hthreshold.trans hlower)) hlow

end LooseHamilton.BootstrapEndpointLowCapture
