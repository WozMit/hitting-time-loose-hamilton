module

public import HittingTimeLooseHamilton.PrivateFrameCountBounds
public import HittingTimeLooseHamilton.MigrationCandidateLower

public section

/-! Actual frame balance captures every low private-test summand. The source
count equality is the source-frame dictionary; the filtered frame mean need
only be at most the outer source mean, not equal to it. -/
noncomputable section
namespace LooseHamilton
open Finset AuxiliaryFrame
variable {V : Type*} [Fintype V] [DecidableEq V]
attribute [local instance] Classical.propDecidable

@[expose] def frameAbnormalCandidates {r : ℕ} {original : SimpleHypergraph V}
    (f : Frame r original) (H : SimpleHypergraph V) (α : ℝ) :=
  f.candidates.filter fun a =>
    α < |(f.completionCount H a : ℝ) /
      ((f.cycleCount H : ℝ) / (((r:ℝ)-1)^2 * f.mu H)) - 1|

theorem frameAbnormalCandidates_card_le {r : ℕ} {original : SimpleHypergraph V}
    (f : Frame r original) (H : SimpleHypergraph V) (α : ℝ)
    (h : ¬ f.candidateBad H α) :
    ((frameAbnormalCandidates f H α).card : ℝ) ≤ α * (f.candidates.card : ℝ) := by
  simpa only [Frame.candidateBad, frameAbnormalCandidates, not_lt] using h

theorem private_low_count_is_abnormal {r : ℕ} (hr : 3 ≤ r)
    {markers original H : SimpleHypergraph V} {S q A R : Finset V} {x t u v : V}
    (h : PrivateRootSplitLegal r markers (allowedEdges r (originalPorts original))
      S q x t A R {u,v})
    (f : Frame r original)
    (hactive : f.active = univ \ insert x S) (hmarkers : f.markers = insert q markers)
    (htports : t ∉ originalPorts original)
    (hsource : f.cycleCount H = completionCount r markers
      (fixedPortHost H (originalPorts original)) (insert x S) q)
    (hsourcepos : 0 < f.cycleCount H) (hμ : 0 < f.mu H)
    (hmean : f.mu H ≤ privateRootSourceMean r H S x)
    (α c : ℝ) (hα : α ≤ 1) (hc : c ≤ (1-α)/((r:ℝ)-1)^2)
    (hlow : (privateCandidateCompletionCount r markers
      (fixedPortHost H (originalPorts original)) S q x (insert t R,u,v) : ℝ) <
        c * (completionCount r markers (fixedPortHost H (originalPorts original))
          (insert x S) q : ℝ) / privateRootSourceMean r H S x) :
    (insert t R,u,v) ∈ frameAbnormalCandidates f H α := by
  apply mem_filter.mpr
  have hlegal := h.frame_candidate hr f hactive hmarkers htports
  refine ⟨mem_filter.mpr ⟨mem_univ _,hlegal⟩,?_⟩
  by_contra hn
  have hbal : |(f.completionCount H (insert t R,u,v) : ℝ) /
      ((f.cycleCount H : ℝ) / (((r:ℝ)-1)^2 * f.mu H)) - 1| ≤ α := le_of_not_gt hn
  have hX : (0 : ℝ) < f.cycleCount H := by exact_mod_cast hsourcepos
  have hlower := Migration.balanced_directed_count_lower hr hX hμ hbal
  have hcoef : 0 ≤ (1-α)/((r:ℝ)-1)^2 := Migration.candidate_lower_coefficient_nonneg hα
  have hμraw : 0 < privateRootSourceMean r H S x := hμ.trans_le hmean
  have hthreshold : c * (f.cycleCount H : ℝ) / privateRootSourceMean r H S x ≤
      ((1-α)/((r:ℝ)-1)^2) * (f.cycleCount H : ℝ) / f.mu H := by
    calc
      _ ≤ ((1-α)/((r:ℝ)-1)^2) * (f.cycleCount H : ℝ) /
          privateRootSourceMean r H S x :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hc hX.le) hμraw.le
      _ ≤ _ := div_le_div_of_nonneg_left (mul_nonneg hcoef hX.le) hμ hmean
  have hcount : (f.completionCount H (insert t R,u,v) : ℝ) ≤
      privateCandidateCompletionCount r markers (fixedPortHost H (originalPorts original))
        S q x (insert t R,u,v) := by
    exact_mod_cast private_frame_completion_le hr h f hactive hmarkers
  rw [← hsource] at hlow
  exact (not_lt_of_ge ((hthreshold.trans hlower).trans hcount)) hlow

/-- The root-test counting bound with its exceptional set now instantiated by
actual abnormal frame candidates, rather than an abstract migration premise. -/
theorem private_bad_root_edges_le_frame_fiber {r : ℕ} (hr : 3 ≤ r)
    (h time : ℕ) (markers original F H : SimpleHypergraph V) (S q : Finset V) (x t : V)
    (f : Frame r original)
    (hactive : f.active = univ \ insert x S) (hmarkers : f.markers = insert q markers)
    (htports : t ∉ originalPorts original)
    (hsource : f.cycleCount H = completionCount r markers
      (fixedPortHost H (originalPorts original)) (insert x S) q)
    (hsourcepos : 0 < f.cycleCount H) (hμ : 0 < f.mu H)
    (hmean : f.mu H ≤ privateRootSourceMean r H S x)
    (α c : ℝ) (hα : α ≤ 1) (hc : c ≤ (1-α)/((r:ℝ)-1)^2) :
    ((registerPrivateRootTest r h time markers S q (originalPorts original) x t c).badSet (F,H)).card ≤
      (privateBadCandidateFiber (frameAbnormalCandidates f H α) t).card +
        (privateRootInvalidEdges r markers (allowedEdges r (originalPorts original)) S q x t).card := by
  apply private_bad_root_edges_card_le
  intro A R u v hlegal hlow
  exact private_low_count_is_abnormal hr hlegal f hactive hmarkers htports hsource
    hsourcepos hμ hmean α c hα hc hlow

end LooseHamilton
