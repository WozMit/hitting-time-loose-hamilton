module

public import HittingTimeLooseHamilton.FrameForwardWitnessFinite
public import HittingTimeLooseHamilton.FrameForwardProbability
public import HittingTimeLooseHamilton.FrameForwardTerminal
public import HittingTimeLooseHamilton.FrameForwardError
public import HittingTimeLooseHamilton.FrameMissingEntropyUniform
public import HittingTimeLooseHamilton.FrameCandidateInstabilityProbability
public import HittingTimeLooseHamilton.FrameSampledAbnormalTail

public section

/-! The pointwise forward witness on every bad inherited-regular source.
The only main-family estimate is the common unconditional survival event. -/
noncomputable section
namespace LooseHamilton.CandidateBalance
open Finset AuxiliaryFrame FrameSurvival Filter FrameScales

/-- A common vanishing error bounds failure of the actual forward witness.
All constants and thresholds precede the source, frame, time and boundary.
The original offset is fixed before the terminal-feasibility threshold. -/
theorem inherited_forward_witness_eventually (r b : ℕ) (hr : 3 ≤ r)
    (C B L offset : ℝ) (hC : 0 < C) (hB : 0 ≤ B) (hL : 0 < L) :
    ∃ Km Kc Kg : ℝ, 0 < Km ∧ 0 < Kc ∧ 0 < Kg ∧
    ∀ᶠ N : ℕ in atTop,
      ∀ (M : ℕ) (ell : Fin N → ℕ) (original : Finset (Finset (Fin N))),
      CoreAdmissible r M ell original offset →
      ∀ (f : Frame r original) (D : Finset (Fin N)), D.card ≤ b →
      ∀ (j h : ℕ) (c : ℝ) (ω : Outcome (Fin N) r M ell),
        4*r ≤ h → M ≤ j → j ≤ (completeEdges (Fin N) r).card →
        InheritedRegularity original j h c C L ω →
        f.entropyBudget (extensionState ω.1 ω.2 j) B →
      let H := extensionState ω.1 ω.2 j
      f.candidateBad H (alpha N) →
      ∃ hτ : batchSize f D H ≤ (unexposed f D H).card,
        1-forwardError r C Km Kc Kg N ≤
          (hostBatchLaw hτ).event (fun T => ForwardWitnessSuccess f D ω.1.val ell H T.val) := by
  obtain ⟨Km,hKm,hmain⟩ := inherited_main_remainder_concentration_eventually r b hr C B hC hB
  obtain ⟨_,Kc,_,hKc,hpersist⟩ := inherited_persistence_probability_eventually r b hr C B hC hB
  obtain ⟨_,Kg,_,hKg,hsampled⟩ := inherited_sampled_bad_tail_eventually r b hr C B L hC hB hL
  refine ⟨Km,Kc,Kg,hKm,hKc,hKg,?_⟩
  filter_upwards [hmain,hpersist,hsampled,
    inherited_terminal_feasibility_eventually r hr C hC offset,
    inherited_remainder_existing_negligible_eventually r b hr C B L hC hB hL,
    inherited_sampling_parameters_eventually r b hr C hC.le,eventual_range]
    with N hm hp hs ht he hparam hR
  intro M ell original hadm f D hD j h c ω hh hMj hj hreg hbudget
  dsimp only
  let H := extensionState ω.1 ω.2 j
  intro hbad
  obtain ⟨htpos,hτ,hmainfail⟩ := hm M ell original offset hadm f D hD j h c L ω hh hMj hj hreg hbudget
  obtain ⟨_,hterminalfail⟩ := ht M ell original hadm ω hreg.1 f D j
  obtain ⟨_,hpersistfail,_⟩ := hp M ell original offset hadm f D hD j h c L ω hh hMj hj hreg hbudget hbad
  obtain ⟨_,hsampledfail,_,_⟩ := hs M ell original offset hadm f D hD j h c ω hh hMj hj hreg hbudget
  have hstatic := he M ell original offset hadm f D hD j h c ω hh hMj hj hreg hbudget
  have hparams := hparam M ell original offset hadm f D hD j h c L ω hMj hj hreg
  obtain ⟨_,_,_,_,_,_,_,_,_,_,hlegal,_⟩ := hparams
  refine ⟨hτ,?_⟩
  have hmainfail' : (hostBatchLaw hτ).event (fun T => ¬ MainCountSurvives f D H T.val) ≤
      survivalFailureBound Km N := by
    simpa only [MainCountSurvives,not_le,survivalFailureBound] using hmainfail
  have hpersistfail' : (hostBatchLaw hτ).event (fun T => ¬(MainCountSurvives f D H T.val →
      alpha N/2*f.candidates.card ≤ ((persistingAbnormalCandidates f D H T.val).card:ℝ))) ≤
      survivalFailureBound Kc N/(alpha N)^2 := by
    simpa only [Classical.not_imp,not_le,survivalFailureBound] using hpersistfail
  have hsampledfail' : (hostBatchLaw hτ).event (fun T => ¬(MainCountSurvives f D H T.val →
      ((sampledBadRoles f D H T.val).card:ℝ) ≤ (alpha N)^2*batchSize f D H)) ≤
      Kg*((1/(alpha N*Real.sqrt (L2 N))+survivalFailureBound 1 N)/(alpha N)^2) := by
    simpa only [Classical.not_imp,not_le,survivalFailureBound,one_mul] using hsampledfail
  have hgood := forward_four_event_lower (hostBatchLaw hτ)
    (fun T => BatchRetainsLower ω.1.val ell T.val)
    (fun T => MainCountSurvives f D H T.val)
    (fun T => MainCountSurvives f D H T.val →
      alpha N/2*f.candidates.card ≤ ((persistingAbnormalCandidates f D H T.val).card:ℝ))
    (fun T => MainCountSurvives f D H T.val →
      ((sampledBadRoles f D H T.val).card:ℝ) ≤ (alpha N)^2*batchSize f D H)
    (fun T => ForwardWitnessSuccess f D ω.1.val ell H T.val)
    (noDeficitError (C*(8*((r:ℝ)-1))) (epsilon/8) N (nu N))
    (survivalFailureBound Km N) (survivalFailureBound Kc N/(alpha N)^2)
    (Kg*((1/(alpha N*Real.sqrt (L2 N))+survivalFailureBound 1 N)/(alpha N)^2))
    hterminalfail hmainfail' hpersistfail' hsampledfail'
    (fun T hterminal hsurvive hper hroles =>
      forwardWitness_of_good_counts f hr D ω.1.val ell H T htpos hR.2.2.2.1.le hlegal
        (hstatic T hsurvive).2 hterminal (hper hsurvive) (hroles hsurvive))
  exact hgood

end LooseHamilton.CandidateBalance
