module

public import HittingTimeLooseHamilton.FrameTinyCompletion
public import HittingTimeLooseHamilton.FrameCandidateTransferActual
public import HittingTimeLooseHamilton.FrameConditionalCompletionRemainder

public section

/-! Tiny completion transfer on the retained-boundary remainder itself. -/
noncomputable section
namespace LooseHamilton.CandidateBalance
open Finset AuxiliaryFrame Filter FrameScales

/-- The source-normal cutoff stated with the common frame normalization. -/
theorem frame_source_normal_large_eventually (r : ℕ) (hr : 3≤r) :
    ∀ᶠ N in atTop, ∀ (original : Finset (Finset (Fin N))) (f : Frame r original)
      (H : SimpleHypergraph (Fin N)) (c : Finset (Fin N) × Fin N × Fin N),
    0 < f.cycleCount H → |frameNormalizedCount f H c-1|≤alpha N/100 →
    (f.cycleCount H:ℝ)*(N:ℝ)^(-(100*(r:ℝ))) ≤ f.completionCount H c :=
  Frame.source_normal_completion_large_eventually r hr

/-- Tiny candidates stay abnormal on the actual remainder on the common
main-count survival event, with no completion-count survival requirement. -/
theorem frame_tiny_remainder_abnormal_eventually (r : ℕ) (hr : 3≤r) :
    ∀ᶠ N in atTop, ∀ (original : Finset (Finset (Fin N))) (f : Frame r original)
      (D : Finset (Fin N)) (H T : SimpleHypergraph (Fin N))
      (c : Finset (Fin N) × Fin N × Fin N),
    T ⊆ unexposed f D H → 0 < (unexposed f D H).card →
    4*f.k≤(unexposed f D H).card →
    4*batchSize f D H≤(unexposed f D H).card →
    (batchSize f D H:ℝ)*f.k/(unexposed f D H).card≤nu N →
    0 < f.cycleCount H →
    (f.completionCount H c:ℝ) < (f.cycleCount H:ℝ)*(N:ℝ)^(-(100*(r:ℝ))) →
    MainCountSurvives f D H T →
    frameNormalizedCount f (rawRemainder f D H T) c ≤ 1/4 ∧
    alpha N/2 < |frameNormalizedCount f (rawRemainder f D H T) c-1| := by
  filter_upwards [Frame.tiny_completion_persists_eventually r hr,eventual_range]
    with N ht hR original f D H T c hT hm hk4 hτ4 hτ hX hY hs
  have hcycle : f.cycleCount (rawRemainder f D H T)=f.cycleCount (H\T) :=
    congrArg Finset.card (rawRemainder_cycleFamily f D H T hT)
  have hcompletion := rawRemainder_completionCount f D H T c hT
  have hmu : f.mu (rawRemainder f D H T)=f.mu (H\T) := by
    unfold Frame.mu Frame.m
    rw [rawRemainder_eq f D H T hT,←f.rawHost_delete H T,rawHost_idempotent]
  have hζ := CandidateLogSurvival.zeta_pos
    (show f.k+batchSize f D H<(unexposed f D H).card by omega)
  have hcenter : 0≤CandidateLogSurvival.zeta (unexposed f D H).card f.k
      (batchSize f D H)*(f.cycleCount H:ℝ) := mul_nonneg hζ.le (Nat.cast_nonneg _)
  have hsmall : alpha N/100000≤1/2 := by linarith [hR.2.2.2.2.1]
  have hhalf : CandidateLogSurvival.zeta (unexposed f D H).card f.k
      (batchSize f D H)*(f.cycleCount H:ℝ)/2≤f.cycleCount (H\T) := by
    unfold MainCountSurvives at hs
    rw [hcycle] at hs
    have hl := (abs_le.mp hs).1
    have hm' := mul_le_mul_of_nonneg_right hsmall hcenter
    linarith
  have hh := ht original f H T c (unexposed f D H).card (batchSize f D H)
    hm hk4 hτ4 hτ hX hY hhalf
  simpa only [frameNormalizedCount,hcycle,hcompletion,hmu] using hh

end LooseHamilton.CandidateBalance
