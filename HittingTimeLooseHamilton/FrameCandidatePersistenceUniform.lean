module

public import HittingTimeLooseHamilton.FrameCandidatePersistence
public import HittingTimeLooseHamilton.FrameCandidatePersistenceScales
public import HittingTimeLooseHamilton.FrameCandidateTransferUniform
public import HittingTimeLooseHamilton.FrameTinyCompletionInherited

public section

noncomputable section
namespace LooseHamilton.CandidateBalance
open Filter Finset AuxiliaryFrame FrameScales FrameSurvival

/-- Actual abnormality persistence for a positive fraction of all legal
candidates. All transfer and negligible-boundary estimates are discharged
from the inherited source data, simultaneously before the frame is chosen. -/
theorem inherited_candidate_persistence_eventually (r b : ℕ) (hr : 3≤r)
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
      f.candidateBad H (alpha N) →
      ∀ T : HostBatch (unexposed f D H) (batchSize f D H),
      MainCountSurvives f D H T.val →
      largeCompletionUnstableFraction f D H T.val≤(alpha N)^2 →
      alpha N/2*f.candidates.card≤(persistingAbnormalCandidates f D H T.val).card := by
  filter_upwards [inherited_candidate_transfer_eventually r b hr C hC,
    inherited_tiny_completion_eventually r b hr C hC,
    inherited_sampling_parameters_eventually r b hr C hC,
    eventually_boundary_fraction_small (4*(b:ℝ)*r) (by positivity),eventual_range]
    with N htransfer htiny hsampling hsmall hR
  intro M ell original offset hadm f D hD j h c L B ω hMj hj hreg hbudget H hbad T hmain hu
  refine persisting_candidates_card f D H T.val hR.2.2.2.1.le hsmall.1 hbad ?_ hu ?_
  · have hs := hsampling M ell original offset hadm f D hD j h c L ω hMj hj hreg
    have hbound := hs.2.2.2.2.2.2.2.2.2.2.2
    have hb : ((f.boundaryCandidates D).card:ℝ)/(f.candidates.card:ℝ)≤alpha N/4 :=
      hbound.trans hsmall.2
    by_cases hz : f.candidates.card=0
    · have hz' : (f.boundaryCandidates D).card=0 := by
        have hh := card_le_card (filter_subset (fun a => ¬Disjoint (a.1∪{a.2.1,a.2.2}) D) f.candidates)
        change (f.boundaryCandidates D).card≤f.candidates.card at hh
        omega
      simp [hz,hz']
    · exact (div_le_iff₀ (by exact_mod_cast (Nat.pos_of_ne_zero hz))).mp hb
  · intro a ha hunstable habad
    have hlegal : f.LegalCandidate a := by simpa [Frame.candidates] using ha
    by_cases hcut : (f.cycleCount H:ℝ)*(N:ℝ)^(-(100*(r:ℝ)))≤f.completionCount H a
    · have hc : CompletionCountSurvives f D H T.val a
          (CandidateLogSurvival.zeta (unexposed f D H).card (f.k-1) (batchSize f D H)) := by
        by_contra hno
        exact hunstable ⟨hlegal,hcut,hno⟩
      exact (htransfer M ell original offset hadm f D hD j h c L B ω hMj hj hreg hbudget
        T.val (mem_powersetCard.mp T.property).1 (mem_powersetCard.mp T.property).2 hmain a hlegal).1
        hcut hc habad
    · exact (htiny M ell original offset hadm f D hD j h c L B ω hMj hj hreg hbudget
        T hmain a (lt_of_not_ge hcut)).2
end LooseHamilton.CandidateBalance
