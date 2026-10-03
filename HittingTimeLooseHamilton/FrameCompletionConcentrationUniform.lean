module

public import HittingTimeLooseHamilton.FrameCompletionConcentrationRate
public import HittingTimeLooseHamilton.FrameCoarseCompletionUniform

public section

/-! The completed uniform completion-survival statement under the original
inherited source conditions. No overlap estimate is assumed. -/
noncomputable section
namespace LooseHamilton.CandidateBalance
open Finset AuxiliaryFrame FrameSurvival Filter FrameScales

/-- Both completion experiments use the actual raw remainder, including retained
boundary edges. Feasibility and positive conditioning are part of the conclusion. -/
@[expose] def CompletionConcentrationBound {N r : ℕ} {original : Finset (Finset (Fin N))}
    (f : Frame r original) (D : Finset (Fin N)) (H : SimpleHypergraph (Fin N))
    (c : Finset (Fin N) × Fin N × Fin N) (K : ℝ) : Prop :=
  ∃ htpos : 1 ≤ batchSize f D H, ∃ hτ : batchSize f D H ≤ (unexposed f D H).card,
    ((hostBatchLaw hτ).event (fun T =>
      (alpha N/100000) * (CandidateLogSurvival.zeta (unexposed f D H).card
        (f.k-1) (batchSize f D H) * f.completionCount H c) <
      |(f.completionCount (rawRemainder f D H T.val) c : ℝ) -
        CandidateLogSurvival.zeta (unexposed f D H).card
          (f.k-1) (batchSize f D H) * f.completionCount H c|) ≤
      K * (L2 N)^(-24/25:ℝ)/(alpha N/100000)^2) ∧
    (∀ he : c.1 ∪ {c.2.1,c.2.2} ∈ unexposed f D H,
      ((hostBatchLaw hτ).condition (fun T => c.1 ∪ {c.2.1,c.2.2} ∈ T.val)
        (candidate_batch_event_pos he htpos hτ)).event (fun T =>
      (alpha N/100000) * (conditionedZeta (unexposed f D H).card
        (batchSize f D H) f.k * f.completionCount H c) <
      |(f.completionCount (rawRemainder f D H T.val) c : ℝ) -
        conditionedZeta (unexposed f D H).card
          (batchSize f D H) f.k * f.completionCount H c|) ≤
      K * (L2 N)^(-24/25:ℝ)/(alpha N/100000)^2)

/-- Large completions concentrate in both required laws. The constant and the
threshold precede every source, frame, time, boundary, exposure and candidate.
All degree, density, feasibility and overlap estimates follow from inherited
regularity, the original entropy budget and the polynomial completion cutoff. -/
theorem inherited_completion_concentration_eventually (r b : ℕ) (hr : 3 ≤ r)
    (C B : ℝ) (hC : 0 < C) (hB : 0 ≤ B) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ N : ℕ in atTop,
      ∀ (M : ℕ) (ell : Fin N → ℕ) (original : Finset (Finset (Fin N)))
        (offset : ℝ), CoreAdmissible r M ell original offset →
      ∀ (f : Frame r original) (D : Finset (Fin N)), D.card ≤ b →
      ∀ (j h : ℕ) (c L : ℝ) (ω : Outcome (Fin N) r M ell),
        4*r ≤ h → M ≤ j → j ≤ (completeEdges (Fin N) r).card →
        InheritedRegularity original j h c C L ω →
        f.entropyBudget (extensionState ω.1 ω.2 j) B →
      ∀ a : Finset (Fin N) × Fin N × Fin N, f.LegalCandidate a →
        (f.cycleCount (extensionState ω.1 ω.2 j):ℝ)*(N:ℝ)^(-(100*(r:ℝ))) ≤
          f.completionCount (extensionState ω.1 ω.2 j) a →
        CompletionConcentrationBound f D (extensionState ω.1 ω.2 j) a K := by
  obtain ⟨K,hK,hO⟩ := inherited_completion_overlap_eventually r hr C B hC hB
  refine ⟨64*((16*((r:ℝ)-1))*K), ?_, ?_⟩
  · have hrR : (3:ℝ) ≤ r := by exact_mod_cast hr
    have hp : 0 < (r:ℝ)-1 := by linarith
    positivity
  filter_upwards [hO, eventually_actual_completion_concentration r b hr K hK.le,
    inherited_sampling_parameters_eventually r b hr C hC.le,
    eventually_ge_atTop 1] with N hON hconc hparam hN
  intro M ell original offset hadm f D hD j h c L ω hh hMj hj hreg hbudget a ha hcut
  let H := extensionState ω.1 ω.2 j
  have hps := hparam M ell original offset hadm f D hD j h c L ω hMj hj hreg
  have hov := hON M ell original offset hadm f j h c L ω hh hMj hj hreg hbudget a ha hcut
  have hcomp := f.completion_nonempty_of_cutoff H a (by simpa only [Fintype.card_fin] using (show 0 < N by omega)) hbudget.1
    (by simpa only [Fintype.card_fin] using hcut)
  obtain ⟨hmu,_,_,_,_,_,htpos,hk4,ht4,_⟩ := hps
  have hτ : batchSize f D H ≤ (unexposed f D H).card := by
    dsimp [H]
    omega
  refine ⟨htpos,hτ,?_⟩
  exact hconc original f D H a hD hbudget.1 ha hcomp hmu hk4 ht4 htpos hov hτ

end LooseHamilton.CandidateBalance
