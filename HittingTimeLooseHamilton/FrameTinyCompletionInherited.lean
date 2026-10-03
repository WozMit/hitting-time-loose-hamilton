module

public import HittingTimeLooseHamilton.FrameTinyCompletionRemainder
public import HittingTimeLooseHamilton.FrameSamplingRefined

public section

/-! The final tiny-completion endpoint, with all sampling hypotheses derived
from the inherited source event. -/
noncomputable section
namespace LooseHamilton.CandidateBalance
open Finset AuxiliaryFrame FrameSurvival Filter FrameScales

/-- Every tiny candidate stays abnormal on the actual main-survival event.
The inherited source assumptions discharge all density and batch constraints;
no completion concentration assumption occurs. -/
theorem inherited_tiny_completion_eventually (r b : ℕ) (hr : 3≤r)
    (C : ℝ) (hC : 0≤C) :
    ∀ᶠ N : ℕ in atTop, ∀ (M : ℕ) (ell : Fin N → ℕ)
      (original : Finset (Finset (Fin N))) (offset : ℝ),
    CoreAdmissible r M ell original offset →
    ∀ (f : Frame r original) (D : Finset (Fin N)), D.card≤b →
    ∀ (j h : ℕ) (c L B : ℝ) (ω : Outcome (Fin N) r M ell),
    M≤j → j≤(completeEdges (Fin N) r).card →
    InheritedRegularity original j h c C L ω →
    f.entropyBudget (extensionState ω.1 ω.2 j) B →
    let H := extensionState ω.1 ω.2 j
    ∀ T : HostBatch (unexposed f D H) (batchSize f D H),
    MainCountSurvives f D H T.val →
    ∀ a : Finset (Fin N) × Fin N × Fin N,
    (f.completionCount H a:ℝ)<(f.cycleCount H:ℝ)*(N:ℝ)^(-(100*(r:ℝ))) →
    frameNormalizedCount f (rawRemainder f D H T.val) a≤1/4 ∧
    alpha N/2 < |frameNormalizedCount f (rawRemainder f D H T.val) a-1| := by
  filter_upwards [frame_tiny_remainder_abnormal_eventually r hr,
    inherited_sampling_parameters_eventually r b hr C hC,eventual_range]
    with N ht hsam hR
  intro M ell original offset hadm f D hD j h c L B ω hMj hj hreg hbudget
  let H := extensionState ω.1 ω.2 j
  change ∀ T : HostBatch (unexposed f D H) (batchSize f D H), _
  intro T hmain a hcut
  have hs := hsam M ell original offset hadm f D hD j h c L ω hMj hj hreg
  obtain ⟨_,_,_,_,hm,hk,_,hk4,ht4,_⟩ := hs
  have hratio := (actual_batch_ratio_bounds f D H (by omega) hm
    (by simpa only [Fintype.card_fin] using hR.2.2.2.2.2.1.le)).2
  simp only [Fintype.card_fin] at hratio
  exact ht original f D H T.val a (mem_powersetCard.mp T.property).1 hm hk4 ht4
    hratio hbudget.1.card_pos hcut hmain

end LooseHamilton.CandidateBalance
