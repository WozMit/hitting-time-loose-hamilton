module

public import HittingTimeLooseHamilton.BootstrapPrivateCandidateCounts
public import HittingTimeLooseHamilton.BootstrapPrivateSourceNormalization
public import HittingTimeLooseHamilton.BootstrapPrivateAbnormalFibers

public section

/-! Item 33.15.4: low registered residual summands are actual abnormal ambient
candidates. Count comparison and normalization are proved adapters, not premises. -/
noncomputable section
namespace LooseHamilton.BootstrapPrivateLowCapture
open Finset BootstrapBases
variable {V : Type} [Fintype V] [DecidableEq V]
variable {r : ℕ} {M : Finset (Finset V)}
attribute [local instance] Classical.propDecidable

/-- The registered threshold is dominated by the balanced-candidate coefficient. -/
theorem threshold_le_balance (α : ℝ) (hα : α ≤ 1/2) :
    1 / (2 * ((r:ℝ)-1)^2) ≤ (1-α) / ((r:ℝ)-1)^2 := by
  have h := div_le_div_of_nonneg_right (show (1/2:ℝ) ≤ 1-α by linarith)
    (sq_nonneg ((r:ℝ)-1))
  simpa only [div_div] using h

/-- A low literal registered summand forces the lifted candidate to be abnormal.
The source count, mean comparison, and directed-to-unrestricted inequality are
all derived from the actual source frame on the chosen base. -/
theorem low_count_is_abnormal (hM : IsPairMatching M) (b : Base M)
    (F : AuxiliaryFrame.Frame r M) (hr : 3 ≤ r) (H : SimpleHypergraph V)
    (hH : H ⊆ completeEdges V r)
    {S q A R : Finset ↥(active b)} {x t u v : ↥(active b)}
    (h : PrivateRootSplitLegal r (restrictEdges (active b) (markers hM b))
      (allowedEdges r (fixedPorts b)) S q x t A R {u,v})
    (hd : F.val.deleted = deleted b ∪ liftEdge (active b) (insert x S))
    (hm : F.markers = insert (liftEdge (active b) q) (markers hM b))
    (hrel : F.val.relative = none) (ht : t.val ∉ originalPorts M)
    (hW : 0 < completionCount r (restrictEdges (active b) (markers hM b))
      (fixedPortHost (inducedHost (active b) H) (fixedPorts b)) (insert x S) q)
    (α : ℝ) (hα : α ≤ 1/2)
    (hlow : (privateCandidateCompletionCount r
      (restrictEdges (active b) (markers hM b))
      (fixedPortHost (inducedHost (active b) H) (fixedPorts b))
      S q x (insert t R,u,v) : ℝ) <
      (1 / (2 * ((r:ℝ)-1)^2)) *
        (completionCount r (restrictEdges (active b) (markers hM b))
          (fixedPortHost (inducedHost (active b) H) (fixedPorts b)) (insert x S) q : ℝ) /
        privateRootSourceMean r (inducedHost (active b) H) S x) :
    (liftEdge (active b) (insert t R),u.val,v.val) ∈ frameAbnormalCandidates F H α := by
  have hlegal := BootstrapPrivateCandidateLifting.frame_candidate hM b F hr h hd hm ht
  have hsource := BootstrapPrivateSourceNormalization.frame_source_count hM b F H hH
    S q x hd hm hrel
  obtain ⟨hμ,hmean,hμraw⟩ := BootstrapPrivateSourceNormalization.positive_source_normalization
    hM b F hr H hH S q x hd hm hrel hW
  have hX : (0:ℝ) < F.cycleCount H := by
    have hw : 0 < F.cycleCount H := by rw [hsource]; exact hW
    exact_mod_cast hw
  apply mem_filter.mpr
  refine ⟨mem_filter.mpr ⟨mem_univ _,hlegal⟩,?_⟩
  by_contra hn
  have hbal : |(F.completionCount H
      (liftEdge (active b) (insert t R),u.val,v.val) : ℝ) /
      ((F.cycleCount H:ℝ) / (((r:ℝ)-1)^2 * F.mu H)) - 1| ≤ α := le_of_not_gt hn
  have hlower := Migration.balanced_directed_count_lower hr hX hμ hbal
  have hcoef : 0 ≤ (1-α)/((r:ℝ)-1)^2 :=
    Migration.candidate_lower_coefficient_nonneg (by linarith)
  have hthreshold : (1 / (2 * ((r:ℝ)-1)^2)) * (F.cycleCount H:ℝ) /
      privateRootSourceMean r (inducedHost (active b) H) S x ≤
      ((1-α)/((r:ℝ)-1)^2) * (F.cycleCount H:ℝ) / F.mu H := by
    calc
      _ ≤ ((1-α)/((r:ℝ)-1)^2) * (F.cycleCount H:ℝ) /
          privateRootSourceMean r (inducedHost (active b) H) S x :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right (threshold_le_balance α hα) hX.le) hμraw.le
      _ ≤ _ := div_le_div_of_nonneg_left (mul_nonneg hcoef hX.le) hμ hmean
  have hcount : (F.completionCount H
      (liftEdge (active b) (insert t R),u.val,v.val) : ℝ) ≤
      privateCandidateCompletionCount r (restrictEdges (active b) (markers hM b))
        (fixedPortHost (inducedHost (active b) H) (fixedPorts b))
        S q x (insert t R,u,v) := by
    exact_mod_cast BootstrapPrivateCandidateCounts.completionCount_le_registered_summand
      hM b F hr H hH h hd hm
  rw [← hsource] at hlow
  exact (not_lt_of_ge ((hthreshold.trans hlower).trans hcount)) hlow

/-- A captured lifted candidate is incident to the ambient target t.val. -/
theorem captured_mem_fiber (b : Base M) (F : AuxiliaryFrame.Frame r M)
    (H : SimpleHypergraph V) (α : ℝ) (R : Finset ↥(active b)) (t u v : ↥(active b))
    (hc : (liftEdge (active b) (insert t R),u.val,v.val) ∈
      frameAbnormalCandidates F H α) :
    (liftEdge (active b) (insert t R),u.val,v.val) ∈
      privateBadCandidateFiber (frameAbnormalCandidates F H α) t.val := by
  apply mem_filter.mpr
  exact ⟨hc, mem_image.mpr ⟨t, mem_insert_self _ _, rfl⟩⟩

end LooseHamilton.BootstrapPrivateLowCapture
