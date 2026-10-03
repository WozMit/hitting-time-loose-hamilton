module

public import HittingTimeLooseHamilton.FrameCandidateInstabilityUniform
public import HittingTimeLooseHamilton.FrameCandidatePersistenceUniform
public import HittingTimeLooseHamilton.FrameMainRemainderConcentration

public section

/-! Probability of failure of abnormal-candidate persistence. -/
noncomputable section
namespace LooseHamilton.CandidateBalance
open Finset AuxiliaryFrame FrameSurvival Filter FrameScales

/-- Persistence fails only through the common main-count event or an excessive
fraction of unstable large completions. All candidate counts use the full legal
candidate denominator. -/
theorem inherited_persistence_probability_eventually (r b : ℕ) (hr : 3≤r)
    (C B : ℝ) (hC : 0<C) (hB : 0≤B) :
    ∃ Kmain Kcompletion : ℝ, 0<Kmain ∧ 0<Kcompletion ∧ ∀ᶠ N : ℕ in atTop,
    ∀ (M : ℕ) (ell : Fin N → ℕ) (original : Finset (Finset (Fin N)))
      (offset : ℝ), CoreAdmissible r M ell original offset →
    ∀ (f : Frame r original) (D : Finset (Fin N)), D.card≤b →
    ∀ (j h : ℕ) (c L : ℝ) (ω : Outcome (Fin N) r M ell),
    4*r≤h → M≤j → j≤(completeEdges (Fin N) r).card →
    InheritedRegularity original j h c C L ω →
    f.entropyBudget (extensionState ω.1 ω.2 j) B →
    let H := extensionState ω.1 ω.2 j
    f.candidateBad H (alpha N) →
    ∃ hτ : batchSize f D H≤(unexposed f D H).card,
      (hostBatchLaw hτ).event (fun T => MainCountSurvives f D H T.val ∧
        ((persistingAbnormalCandidates f D H T.val).card:ℝ)<
          alpha N/2*f.candidates.card) ≤
        (Kcompletion*(L2 N)^(-24/25:ℝ)/(alpha N/100000)^2)/(alpha N)^2 ∧
      (hostBatchLaw hτ).event (fun T =>
        ((persistingAbnormalCandidates f D H T.val).card:ℝ)<
          alpha N/2*f.candidates.card) ≤
        Kmain*(L2 N)^(-24/25:ℝ)/(alpha N/100000)^2 +
          (Kcompletion*(L2 N)^(-24/25:ℝ)/(alpha N/100000)^2)/(alpha N)^2 := by
  obtain ⟨Km,hKm,hm⟩ := inherited_main_remainder_concentration_eventually r b hr C B hC hB
  obtain ⟨Kc,hKc,hc⟩ := inherited_large_instability_eventually r b hr C B hC hB
  refine ⟨Km,Kc,hKm,hKc,?_⟩
  filter_upwards [hm,hc,inherited_candidate_persistence_eventually r b hr C hC.le]
    with N hmain hinst hpersist
  intro M ell original offset hadm f D hD j h c L ω hh hMj hj hreg hbudget
  let H := extensionState ω.1 ω.2 j
  change f.candidateBad H (alpha N) → _
  intro hbad
  obtain ⟨hτ,_,hfailure⟩ := hinst M ell original offset hadm f D hD j h c L ω
    hh hMj hj hreg hbudget
  obtain ⟨_,_,hmainfailure⟩ := hmain M ell original offset hadm f D hD j h c L ω
    hh hMj hj hreg hbudget
  have hp := hpersist M ell original offset hadm f D hD j h c L B ω hMj hj hreg hbudget hbad
  have hsubset (T : HostBatch (unexposed f D H) (batchSize f D H))
      (hT : MainCountSurvives f D H T.val ∧
        ((persistingAbnormalCandidates f D H T.val).card:ℝ)<alpha N/2*f.candidates.card) :
      (alpha N)^2<largeCompletionUnstableFraction f D H T.val := by
    by_contra hn
    exact (not_lt_of_ge (hp T hT.1 (le_of_not_gt hn))) hT.2
  have hfirst := ((hostBatchLaw hτ).event_mono hsubset).trans hfailure
  refine ⟨hτ,hfirst,?_⟩
  have hmain' : (hostBatchLaw hτ).event (fun T => ¬MainCountSurvives f D H T.val) ≤
      Km*(L2 N)^(-24/25:ℝ)/(alpha N/100000)^2 := by
    simpa only [MainCountSurvives,not_le] using hmainfailure
  have hunion := (hostBatchLaw hτ).finite_union_bound (fun t : Bool =>
    if t then (fun T => ¬MainCountSurvives f D H T.val)
    else (fun T => MainCountSurvives f D H T.val ∧
      ((persistingAbnormalCandidates f D H T.val).card:ℝ)<alpha N/2*f.candidates.card))
  have hevent : (hostBatchLaw hτ).event (fun T =>
      ((persistingAbnormalCandidates f D H T.val).card:ℝ)<alpha N/2*f.candidates.card) ≤
    (hostBatchLaw hτ).event (fun T => ∃ t : Bool,
      (if t then (fun T => ¬MainCountSurvives f D H T.val)
      else (fun T => MainCountSurvives f D H T.val ∧
        ((persistingAbnormalCandidates f D H T.val).card:ℝ)<alpha N/2*f.candidates.card)) T) := by
    apply FiniteEntropy.Law.event_mono
    intro T hT
    by_cases hs : MainCountSurvives f D H T.val
    · exact ⟨false,by simp [hs,hT]⟩
    · exact ⟨true,by simp [hs]⟩
  have hu := hevent.trans hunion
  simp only [Fintype.sum_bool, Bool.false_eq_true, if_false, if_true] at hu
  exact hu.trans (add_le_add hmain' hfirst)

end LooseHamilton.CandidateBalance
