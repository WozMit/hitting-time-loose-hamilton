module

public import HittingTimeLooseHamilton.BootstrapFrameCounts
public import HittingTimeLooseHamilton.CompletionMaximumIntersection

public section

/-! The original-frame candidate statistic is literally the cycle completion
count, after adding the two relative directions. -/
noncomputable section
namespace LooseHamilton.AuxiliaryFrame.Frame
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {r : ℕ} {original : Finset (Finset V)}

theorem original_cycleCount (F : Frame r original) (hr : 3 ≤ r)
    (hrel : F.val.relative = none) (hdel : F.val.deleted = ∅)
    (hmarkers : F.markers = original) (H : Finset (Finset V)) :
    F.cycleCount H = LooseHamilton.cycleCount r original H (originalPorts original) := by
  rw [F.cycleCount_no_relative hrel H]
  have ha : F.active = univ := by simp [active,Code.active,hdel]
  rw [ha,hmarkers]
  unfold cycleOnCount LooseHamilton.cycleCount
  rw [cycleFamily_eq_unrestricted_inter r original H (originalPorts original) hr]
  congr 1
  ext E
  rw [mem_cycleOnFamily,mem_unrestrictedCycleFamily _ _ _ _ hr]
  exact and_congr isMixedCycleOn_univ_iff Iff.rfl

theorem original_completionCount_two_directions (F : Frame r original) (hr : 3 ≤ r)
    (hrel : F.val.relative = none) (hdel : F.val.deleted = ∅)
    (hmarkers : F.markers = original) (H : Finset (Finset V))
    (P : Finset V) (u v : V) (huv : u ≠ v) :
    F.completionCount H (P,u,v) + F.completionCount H (P,v,u) =
      LooseHamilton.completionCount r original
        (H ∩ allowedEdges r (originalPorts original)) P {u,v} := by
  rw [F.completionCount_two_directions hr hrel H P u v huv]
  simp only [active,Code.active,hdel,sdiff_empty,hmarkers,LooseHamilton.completionCount]

/-- Candidate balance bounds a genuine completion maximum whenever the actual
mobility-large family has the required cardinality. -/
theorem original_maximum_le (F : Frame r original) (hr : 3 ≤ r)
    (hrel : F.val.relative = none) (hdel : F.val.deleted = ∅)
    (hmarkers : F.markers = original) (H : Finset (Finset V))
    (α κ B : ℝ) (hκ : 0 < κ)
    (hscale : 0 < (LooseHamilton.cycleCount r original H (originalPorts original):ℝ)/
      (((r:ℝ)-1)^2*F.mu H))
    (hbalance : ¬ F.candidateBad H α)
    (large : Finset (Finset V × V × V)) (hlegal : large ⊆ F.candidates)
    (hlarge : ∀ a ∈ large, κ*B ≤ (LooseHamilton.completionCount r original
      (H ∩ allowedEdges r (originalPorts original)) a.1 {a.2.1,a.2.2}:ℝ))
    (hsize : ((F.candidates \ large).card:ℝ)+2*α*(F.candidates.card:ℝ) < F.candidates.card) :
    B ≤ (2*(1+α)/κ)*((LooseHamilton.cycleCount r original H (originalPorts original):ℝ)/
      (((r:ℝ)-1)^2*F.mu H)) := by
  classical
  rw [← F.original_cycleCount hr hrel hdel hmarkers H] at hscale ⊢
  apply F.maximum_le_of_candidate_balance H α κ B hκ hscale hbalance large ?_ hsize
  intro a ha
  have hc := ((mem_filter.mp (hlegal ha)).2 : F.LegalCandidate a)
  have huv : a.2.1 ≠ a.2.2 := by
    intro heq
    have hp := hc.1.pair_card
    simp [heq] at hp
  have he := F.original_completionCount_two_directions hr hrel hdel hmarkers H
    a.1 a.2.1 a.2.2 huv
  change κ*B ≤ (F.completionCount H (a.1,a.2.1,a.2.2):ℝ) +
    (F.completionCount H (a.1,a.2.2,a.2.1):ℝ)
  rw [← Nat.cast_add,he]
  exact hlarge a ha

end LooseHamilton.AuxiliaryFrame.Frame
