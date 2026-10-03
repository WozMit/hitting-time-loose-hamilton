module

public import HittingTimeLooseHamilton.FrameCandidateTransferActual
public import HittingTimeLooseHamilton.FrameRestrictedNormalizationUniform
public import HittingTimeLooseHamilton.FrameRemainderParameters

public section

/-! Uniform normalized-candidate transfer on the actual retained-boundary
remainder. All normalization and density errors are derived from the source. -/
noncomputable section
namespace LooseHamilton.CandidateBalance
open Finset AuxiliaryFrame FrameSurvival Filter FrameScales

/-- The normalized count transfers under the survival events already established
in item 30.10. The main event remains the same unconditional cycle event even
in the candidate-conditioned completion branch. -/
theorem inherited_candidate_transfer_eventually (r b : ℕ) (hr : 3 ≤ r)
    (C : ℝ) (hC : 0 ≤ C) :
    ∀ᶠ N : ℕ in atTop, ∀ (M : ℕ) (ell : Fin N → ℕ)
      (original : Finset (Finset (Fin N))) (offset : ℝ),
      CoreAdmissible r M ell original offset →
      ∀ (f : Frame r original) (D : Finset (Fin N)), D.card ≤ b →
      ∀ (j h : ℕ) (c L B : ℝ) (ω : Outcome (Fin N) r M ell),
      M ≤ j → j ≤ (completeEdges (Fin N) r).card →
      InheritedRegularity original j h c C L ω →
      f.entropyBudget (extensionState ω.1 ω.2 j) B →
      let H := extensionState ω.1 ω.2 j
      ∀ T : SimpleHypergraph (Fin N), T ⊆ unexposed f D H →
      T.card = batchSize f D H → MainCountSurvives f D H T →
      ∀ a : Finset (Fin N) × Fin N × Fin N, f.LegalCandidate a →
      (((f.cycleCount H:ℝ)*(N:ℝ)^(-(100*(r:ℝ))) ≤ f.completionCount H a) →
        CompletionCountSurvives f D H T a
          (CandidateLogSurvival.zeta (unexposed f D H).card (f.k-1) (batchSize f D H)) →
        alpha N < |frameNormalizedCount f H a-1| →
        alpha N/2 < |frameNormalizedCount f (rawRemainder f D H T) a-1|) ∧
      (a.1 ∪ {a.2.1,a.2.2} ∈ T →
        CompletionCountSurvives f D H T a
          (conditionedZeta (unexposed f D H).card (batchSize f D H) f.k) →
        |frameNormalizedCount f H a-1| ≤ alpha N/100 →
        |frameNormalizedCount f (rawRemainder f D H T) a-1| ≤ alpha N/4) := by
  filter_upwards [inherited_normalization_alpha r b hr C hC,
    inherited_sampling_parameters_eventually r b hr C hC,
    eventual_range, eventually_ge_atTop (1:ℕ)] with N hrat hsam hR hN
  intro M ell original offset hadm f D hD j h c L B ω hMj hj hreg hbudget
  dsimp only
  let H := extensionState ω.1 ω.2 j
  intro T hT hTcard hmain a _ha
  have hs := hsam M ell original offset hadm f D hD j h c L ω hMj hj hreg
  have hn := hrat M ell original offset hadm f D hD j h c L ω hMj hj hreg
  change _ ∧ _ at hn
  obtain ⟨hmu,_,_,_,hm0,hk,ht,hk4,ht4,_⟩ := hs
  change L1 N/2 ≤ f.mu H at hmu
  change 0 < (unexposed f D H).card at hm0
  change 1 ≤ batchSize f D H at ht
  change 4*f.k ≤ (unexposed f D H).card at hk4
  change 4*batchSize f D H ≤ (unexposed f D H).card at ht4
  have hm : 0 < f.m H := by
    have hsub : (unexposed f D H).card ≤ f.m H := by
      rw [unexposed_eq_surviving]
      exact card_le_card (filter_subset _ _)
    omega
  have hmuPos : 0 < f.mu H := lt_of_lt_of_le (div_pos hR.1 (by norm_num)) hmu
  have hmr := rawRemainder_mu_ratio f (by omega : 0 < r) D H T hT hm
  rw [hTcard] at hmr
  have hz0 : 0 < CandidateLogSurvival.zeta (unexposed f D H).card f.k (batchSize f D H) :=
    CandidateLogSurvival.zeta_pos (by omega)
  have hz1 : 0 < CandidateLogSurvival.zeta (unexposed f D H).card (f.k-1) (batchSize f D H) :=
    CandidateLogSurvival.zeta_pos (by omega)
  have hzhat : 0 < conditionedZeta (unexposed f D H).card (batchSize f D H) f.k :=
    conditionedZeta_pos hk ht (by omega)
  have hr1 : |(CandidateLogSurvival.zeta (unexposed f D H).card (f.k-1) (batchSize f D H) /
      CandidateLogSurvival.zeta (unexposed f D H).card f.k (batchSize f D H)) *
      (f.mu (rawRemainder f D H T)/f.mu H)-1| ≤ alpha N/100000 := by
    rw [hmr]
    exact hn.1
  have hrhat : |(conditionedZeta (unexposed f D H).card (batchSize f D H) f.k /
      CandidateLogSurvival.zeta (unexposed f D H).card f.k (batchSize f D H)) *
      (f.mu (rawRemainder f D H T)/f.mu H)-1| ≤ alpha N/100000 := by
    rw [hmr]
    exact hn.2
  constructor
  · intro hcut hcomp hbad
    have hY := f.completion_nonempty_of_cutoff H a (by simpa only [Fintype.card_fin] using (show 0 < N by omega)) hbudget.1
      (by simpa only [Fintype.card_fin] using hcut)
    exact frame_abnormality_of_survival f D H T a _ hbudget.1 (card_pos.mpr hY)
      hmuPos hz1 hz0 hR.2.2.2.1 hR.2.2.2.2.1.le hmain hcomp hr1 hbad
  · intro _he hcomp hnormal
    exact frame_normality_of_survival f D H T a _ hbudget.1 hmuPos hzhat hz0
      hR.2.2.2.1 hR.2.2.2.2.1.le hmain hcomp hrhat hnormal

end LooseHamilton.CandidateBalance
