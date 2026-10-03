module

public import HittingTimeLooseHamilton.FrameSampledAbnormalDefinitions
public import HittingTimeLooseHamilton.FrameCandidateTransferUniform
public import HittingTimeLooseHamilton.FrameTinyCompletionRemainder
public import HittingTimeLooseHamilton.FrameCompletionConcentrationUniform

public section

/-! Candidate-conditioned failure bounds with the common main event retained
as an indicator. No conditional main-concentration statement is used. -/
noncomputable section
namespace LooseHamilton.CandidateBalance
open Finset AuxiliaryFrame FrameSurvival Filter FrameScales

/-- Under a source-normal candidate, remainder abnormality on the common main
survival event forces failure of conditional completion concentration. -/
theorem inherited_sampled_normal_bad_eventually (r b : ℕ) (hr : 3 ≤ r)
    (C B : ℝ) (hC : 0 < C) (hB : 0 ≤ B) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ N : ℕ in atTop,
      ∀ (M : ℕ) (ell : Fin N → ℕ) (original : Finset (Finset (Fin N)))
        (offset : ℝ), CoreAdmissible r M ell original offset →
      ∀ (f : Frame r original) (D : Finset (Fin N)), D.card ≤ b →
      ∀ (j h : ℕ) (c L : ℝ) (ω : Outcome (Fin N) r M ell),
        4*r ≤ h → M ≤ j → j ≤ (completeEdges (Fin N) r).card →
        InheritedRegularity original j h c C L ω →
        f.entropyBudget (extensionState ω.1 ω.2 j) B →
      let H := extensionState ω.1 ω.2 j
      ∀ (a : Finset (Fin N) × Fin N × Fin N), f.LegalCandidate a →
      |frameNormalizedCount f H a-1| ≤ alpha N/100 →
      ∀ (he : a.1 ∪ {a.2.1,a.2.2} ∈ unexposed f D H)
        (htpos : 1 ≤ batchSize f D H) (hτ : batchSize f D H ≤ (unexposed f D H).card),
      ((hostBatchLaw hτ).condition (fun T => a.1 ∪ {a.2.1,a.2.2} ∈ T.val)
        (candidate_batch_event_pos he htpos hτ)).event (fun T =>
        MainCountSurvives f D H T.val ∧
        alpha N/4 < |frameNormalizedCount f (rawRemainder f D H T.val) a-1|) ≤
      K*(L2 N)^(-24/25:ℝ)/(alpha N/100000)^2 := by
  obtain ⟨K,hK,hconc⟩ := inherited_completion_concentration_eventually r b hr C B hC hB
  refine ⟨K,hK,?_⟩
  filter_upwards [hconc, inherited_candidate_transfer_eventually r b hr C hC.le,
    frame_source_normal_large_eventually r hr] with N hco htr hlarge
  intro M ell original offset hadm f D hD j h c L ω hh hMj hj hreg hbudget
  dsimp only
  let H := extensionState ω.1 ω.2 j
  intro a ha hnormal he htpos hτ
  have hcut := hlarge original f H a (card_pos.mpr hbudget.1) hnormal
  obtain ⟨_,_,_,hcond⟩ := hco M ell original offset hadm f D hD j h c L ω hh hMj hj hreg hbudget a ha hcut
  have hcond' := hcond he
  have hfail :
      ((hostBatchLaw hτ).condition (fun T => a.1 ∪ {a.2.1,a.2.2} ∈ T.val)
        (candidate_batch_event_pos he htpos hτ)).event (fun T =>
        ¬ CompletionCountSurvives f D H T.val a
          (conditionedZeta (unexposed f D H).card (batchSize f D H) f.k)) ≤
      K*(L2 N)^(-24/25:ℝ)/(alpha N/100000)^2 := by
    simpa only [CompletionCountSurvives, not_le] using hcond'
  apply le_trans _ hfail
  rw [condition_event_eq_joint, condition_event_eq_joint]
  apply div_le_div_of_nonneg_right _ (FiniteEntropy.Law.event_nonneg _ _)
  apply FiniteEntropy.Law.event_mono
  intro T hbad
  refine ⟨hbad.1,?_⟩
  intro hsurv
  have ht := (mem_powersetCard.mp T.property)
  have htransfer := htr M ell original offset hadm f D hD j h c L B ω hMj hj hreg hbudget
    T.val ht.1 ht.2 hbad.2.1 a ha
  exact (not_lt_of_ge (htransfer.2 hbad.1 hsurv hnormal)) hbad.2.2

end LooseHamilton.CandidateBalance
