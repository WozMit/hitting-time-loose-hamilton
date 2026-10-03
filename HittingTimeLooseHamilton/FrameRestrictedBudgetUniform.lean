module

public import HittingTimeLooseHamilton.FrameRestrictedBudget
public import HittingTimeLooseHamilton.FrameSamplingRefined

public section

noncomputable section
namespace LooseHamilton.CandidateBalance
open Filter Finset AuxiliaryFrame FrameScales FrameSurvival

/-- Main survival preserves the imposed budget with coefficient B+1 on the
actual retained-boundary remainder, with no extra density or error premise.
The original vertex count is used throughout the entropy error. -/
theorem inherited_restricted_budget_eventually (r b : ℕ) (hr : 3≤r)
    (C : ℝ) (hC : 0≤C) :
    ∀ᶠ N : ℕ in atTop,
      ∀ (M : ℕ) (ell : Fin N → ℕ) (original : Finset (Finset (Fin N)))
        (offset : ℝ), CoreAdmissible r M ell original offset →
      ∀ (f : Frame r original) (D : Finset (Fin N)), D.card≤b →
      ∀ (j h : ℕ) (c L B : ℝ) (ω : Outcome (Fin N) r M ell),
        M≤j → j≤(completeEdges (Fin N) r).card →
        InheritedRegularity original j h c C L ω →
        f.entropyBudget (extensionState ω.1 ω.2 j) B →
      let H := extensionState ω.1 ω.2 j
      ∀ T : HostBatch (unexposed f D H) (batchSize f D H),
        |(f.cycleCount (rawRemainder f D H T.val):ℝ)-
          CandidateLogSurvival.zeta (unexposed f D H).card f.k (batchSize f D H)*
            f.cycleCount H| ≤
          (alpha N/100000)*(CandidateLogSurvival.zeta (unexposed f D H).card
            f.k (batchSize f D H)*f.cycleCount H) →
        0<f.cycleCount (rawRemainder f D H T.val) ∧
          f.entropyBudget (rawRemainder f D H T.val) (B+1) := by
  filter_upwards [inherited_sampling_parameters_eventually r b hr C hC,
    eventually_restricted_budget_error,FrameScales.eventual_range]
    with N hp he hR
  intro M ell original offset hadm f D hD j h c L B ω hMj hj hreg hb H T hs
  have hpar := hp M ell original offset hadm f D hD j h c L ω hMj hj hreg
  obtain ⟨hμ,hNk,hkN,hratio,hm,hk,ht,hk4,ht4,hrest⟩ := hpar
  have htSub := (mem_powersetCard.mp T.property).1
  have hc : f.cycleCount (rawRemainder f D H T.val)=f.cycleCount (H\T.val) :=
    congrArg Finset.card (rawRemainder_cycleFamily f D H T.val htSub)
  rw [hc] at hs ⊢
  have hx := actual_batch_ratio_bounds f D H (by omega) hm
    (by simpa only [Fintype.card_fin] using hR.2.2.2.2.2.1.le)
  simp only [Fintype.card_fin] at hx
  have hres := f.entropyBudget_after_restricted_survival hr H T.val hm hk4 ht4
    hx.2 he.1 he.2.1 hb hs (by simpa only [Fintype.card_fin] using he.2.2)
  refine ⟨hres.1,?_⟩
  rw [rawRemainder_eq f D H T.val htSub, ← f.rawHost_delete,
    f.entropyBudget_rawHost]
  exact hres.2
end LooseHamilton.CandidateBalance
