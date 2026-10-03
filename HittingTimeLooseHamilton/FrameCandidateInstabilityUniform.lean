module

public import HittingTimeLooseHamilton.FrameCandidateInstability
public import HittingTimeLooseHamilton.FrameCompletionConcentrationUniform
public import HittingTimeLooseHamilton.FrameSamplingParameters

public section

/-! Averaging completion failures over the full legal candidate denominator. -/
noncomputable section
namespace LooseHamilton.CandidateBalance
open Finset AuxiliaryFrame FrameSurvival Filter FrameScales

/-- Individual completion concentration and Remark 7.2 give expectation and
Markov bounds for the fraction of unstable large candidates. There is no
independence assumption or union bound over the candidates. -/
theorem inherited_large_instability_eventually (r b : ℕ) (hr : 3≤r)
    (C B : ℝ) (hC : 0<C) (hB : 0≤B) :
    ∃ K : ℝ, 0<K ∧ ∀ᶠ N : ℕ in atTop,
    ∀ (M : ℕ) (ell : Fin N → ℕ) (original : Finset (Finset (Fin N)))
      (offset : ℝ), CoreAdmissible r M ell original offset →
    ∀ (f : Frame r original) (D : Finset (Fin N)), D.card≤b →
    ∀ (j h : ℕ) (c L : ℝ) (ω : Outcome (Fin N) r M ell),
    4*r≤h → M≤j → j≤(completeEdges (Fin N) r).card →
    InheritedRegularity original j h c C L ω →
    f.entropyBudget (extensionState ω.1 ω.2 j) B →
    let H := extensionState ω.1 ω.2 j
    ∃ hτ : batchSize f D H≤(unexposed f D H).card,
      (hostBatchLaw hτ).finiteMean (fun T => largeCompletionUnstableFraction f D H T.val) ≤
        K*(L2 N)^(-24/25:ℝ)/(alpha N/100000)^2 ∧
      (hostBatchLaw hτ).event (fun T =>
        (alpha N)^2 < largeCompletionUnstableFraction f D H T.val) ≤
        (K*(L2 N)^(-24/25:ℝ)/(alpha N/100000)^2)/(alpha N)^2 := by
  obtain ⟨K,hK,hconc⟩ := inherited_completion_concentration_eventually r b hr C B hC hB
  refine ⟨K,hK,?_⟩
  filter_upwards [hconc,inherited_sampling_parameters_eventually r b hr C hC.le,eventual_range]
    with N hc hs hR
  intro M ell original offset hadm f D hD j h c L ω hh hMj hj hreg hbudget
  let H := extensionState ω.1 ω.2 j
  have hps := hs M ell original offset hadm f D hD j h c L ω hMj hj hreg
  obtain ⟨_,_,_,_,_,_,_,_,ht4,_⟩ := hps
  have hτ : batchSize f D H≤(unexposed f D H).card := by dsimp [H]; omega
  refine ⟨hτ,?_⟩
  let p₀ := K*(L2 N)^(-24/25:ℝ)/(alpha N/100000)^2
  have hp₀ : 0≤p₀ := div_nonneg
    (mul_nonneg hK.le (Real.rpow_nonneg hR.2.1.le _)) (sq_nonneg _)
  have hi : ∀ a ∈ f.candidates,
      (hostBatchLaw hτ).event (fun T => LargeCompletionUnstable f D H a T.val)≤p₀ := by
    intro a _ha
    by_cases hlegal : f.LegalCandidate a
    · by_cases hlarge : (f.cycleCount H:ℝ)*(N:ℝ)^(-(100*(r:ℝ)))≤f.completionCount H a
      · obtain ⟨_,_,hbound,_⟩ := hc M ell original offset hadm f D hD j h c L ω
          hh hMj hj hreg hbudget a hlegal hlarge
        apply le_trans ((hostBatchLaw hτ).event_mono (fun T hT => ?_)) hbound
        exact lt_of_not_ge hT.2.2
      · have he : (hostBatchLaw hτ).event (fun T => LargeCompletionUnstable f D H a T.val)=0 := by
          simp [FiniteEntropy.Law.event,LargeCompletionUnstable,hlarge]
        rw [he]; exact hp₀
    · have he : (hostBatchLaw hτ).event (fun T => LargeCompletionUnstable f D H a T.val)=0 := by
        simp [FiniteEntropy.Law.event,LargeCompletionUnstable,hlegal]
      rw [he]; exact hp₀
  have hm := (hostBatchLaw hτ).mean_unstableFraction_le f.candidates
    (fun a T => LargeCompletionUnstable f D H a T.val) hp₀ hi
  have ht := (hostBatchLaw hτ).unstableFraction_tail_le f.candidates
    (fun a T => LargeCompletionUnstable f D H a T.val) (sq_pos_of_pos hR.2.2.2.1) hp₀ hi
  exact ⟨hm,ht⟩

end LooseHamilton.CandidateBalance
