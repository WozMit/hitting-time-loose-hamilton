module

public import HittingTimeLooseHamilton.FrameCandidateTransferScalar
public import HittingTimeLooseHamilton.FrameCompletionConcentrationUniform

public section

/-! Actual count predicates and finite transfer on a retained-boundary remainder. -/
noncomputable section
namespace LooseHamilton.CandidateBalance
open Finset AuxiliaryFrame FrameSurvival
variable {N r : ℕ} {original : Finset (Finset (Fin N))}

/-- The literal directed-candidate normalization of the manuscript. -/
@[expose] def frameNormalizedCount (f : Frame r original) (H : SimpleHypergraph (Fin N))
    (c : Finset (Fin N) × Fin N × Fin N) : ℝ :=
  candidateNormalizedCount (f.cycleCount H) (f.completionCount H c) (f.mu H) (((r:ℝ)-1)^2)

/-- The common unconditioned main-family survival event. -/
@[expose] def MainCountSurvives (f : Frame r original) (D : Finset (Fin N))
    (H T : SimpleHypergraph (Fin N)) : Prop :=
  |(f.cycleCount (rawRemainder f D H T):ℝ) -
      CandidateLogSurvival.zeta (unexposed f D H).card f.k (batchSize f D H)*f.cycleCount H| ≤
    (FrameScales.alpha N/100000)*
      (CandidateLogSurvival.zeta (unexposed f D H).card f.k (batchSize f D H)*f.cycleCount H)

/-- Completion survival at its specified exact hypergeometric center. -/
@[expose] def CompletionCountSurvives (f : Frame r original) (D : Finset (Fin N))
    (H T : SimpleHypergraph (Fin N)) (c : Finset (Fin N) × Fin N × Fin N)
    (z : ℝ) : Prop :=
  |(f.completionCount (rawRemainder f D H T) c:ℝ)-z*f.completionCount H c| ≤
    (FrameScales.alpha N/100000)*(z*f.completionCount H c)

lemma source_normal_completion_pos (f : Frame r original) (H : SimpleHypergraph (Fin N))
    (c : Finset (Fin N) × Fin N × Fin N) (hα : FrameScales.alpha N ≤ 1)
    (hn : |frameNormalizedCount f H c-1| ≤ FrameScales.alpha N/100) :
    0 < f.completionCount H c := by
  by_contra h
  have hz : f.completionCount H c = 0 := by omega
  simp only [frameNormalizedCount, candidateNormalizedCount, hz, Nat.cast_zero,
    zero_div, zero_sub, abs_neg, abs_one] at hn
  linarith

/-- Finite actual abnormality transfer; the eventual theorem below discharges
the combined normalization estimate from inherited source parameters. -/
theorem frame_abnormality_of_survival (f : Frame r original)
    (D : Finset (Fin N)) (H T : SimpleHypergraph (Fin N))
    (c : Finset (Fin N) × Fin N × Fin N) (z : ℝ)
    (hX : (f.cycleFamily H).Nonempty) (hY : 0 < f.completionCount H c)
    (hmu : 0 < f.mu H) (hz : 0 < z)
    (hζ : 0 < CandidateLogSurvival.zeta (unexposed f D H).card f.k (batchSize f D H))
    (hα : 0 < FrameScales.alpha N) (hα1 : FrameScales.alpha N ≤ 1)
    (hmain : MainCountSurvives f D H T) (hcomp : CompletionCountSurvives f D H T c z)
    (hratio : |(z / CandidateLogSurvival.zeta (unexposed f D H).card f.k (batchSize f D H)) *
      (f.mu (rawRemainder f D H T)/f.mu H)-1| ≤ FrameScales.alpha N/100000)
    (habnormal : FrameScales.alpha N < |frameNormalizedCount f H c-1|) :
    FrameScales.alpha N/2 < |frameNormalizedCount f (rawRemainder f D H T) c-1| := by
  exact candidate_abnormality_combined _ _ _ _ _ _ _ _ _ _
    (Nat.cast_pos.mpr (card_pos.mpr hX)) (Nat.cast_pos.mpr hY) hmu hζ hz (sq_nonneg _)
    hα hα1 hmain hcomp hratio habnormal

/-- Finite actual normality transfer, using the same main-survival event. -/
theorem frame_normality_of_survival (f : Frame r original)
    (D : Finset (Fin N)) (H T : SimpleHypergraph (Fin N))
    (c : Finset (Fin N) × Fin N × Fin N) (z : ℝ)
    (hX : (f.cycleFamily H).Nonempty) (hmu : 0 < f.mu H) (hz : 0 < z)
    (hζ : 0 < CandidateLogSurvival.zeta (unexposed f D H).card f.k (batchSize f D H))
    (hα : 0 < FrameScales.alpha N) (hα1 : FrameScales.alpha N ≤ 1)
    (hmain : MainCountSurvives f D H T) (hcomp : CompletionCountSurvives f D H T c z)
    (hratio : |(z / CandidateLogSurvival.zeta (unexposed f D H).card f.k (batchSize f D H)) *
      (f.mu (rawRemainder f D H T)/f.mu H)-1| ≤ FrameScales.alpha N/100000)
    (hnormal : |frameNormalizedCount f H c-1| ≤ FrameScales.alpha N/100) :
    |frameNormalizedCount f (rawRemainder f D H T) c-1| ≤ FrameScales.alpha N/4 := by
  exact candidate_normality_combined _ _ _ _ _ _ _ _ _ _
    (Nat.cast_pos.mpr (card_pos.mpr hX))
    (Nat.cast_pos.mpr (source_normal_completion_pos f H c hα1 hnormal)) hmu hζ hz
    hα hα1 hmain hcomp hratio hnormal

end LooseHamilton.CandidateBalance
