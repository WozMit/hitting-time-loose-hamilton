module

public import HittingTimeLooseHamilton.FrameRemainderEntropyUniform
public import HittingTimeLooseHamilton.FrameRemainderRegularityUniform
public import HittingTimeLooseHamilton.FrameRestrictedBudgetUniform
public import HittingTimeLooseHamilton.FrameEntropyWindowEnlargement

public section

noncomputable section
namespace LooseHamilton.CandidateBalance
open Filter Finset AuxiliaryFrame FrameScales FrameSurvival

/-- On the one unconditional main-survival event, the actual retained-boundary
remainder has its imposed budget, density, full partition regularity and static
entropy exceptional-role estimate. Every threshold precedes the batch and t. -/
theorem inherited_remainder_static_entropy_eventually (r b : ℕ) (hr : 3≤r)
    (C B L : ℝ) (hC : 0<C) (hB : 0≤B) (hL : 0<L) :
    ∃ K : ℝ, 0<K ∧ ∀ᶠ N : ℕ in atTop,
      ∀ (M : ℕ) (ell : Fin N→ℕ) (original : Finset (Finset (Fin N))) (offset : ℝ),
        CoreAdmissible r M ell original offset →
      ∀ (f : Frame r original) (D : Finset (Fin N)), D.card≤b →
      ∀ (j h : ℕ) (c : ℝ) (ω : Outcome (Fin N) r M ell),
        4*r≤h → M≤j → j≤(completeEdges (Fin N) r).card →
        InheritedRegularity original j h c C L ω →
        f.entropyBudget (extensionState ω.1 ω.2 j) B →
      let H := extensionState ω.1 ω.2 j
      ∀ T : HostBatch (unexposed f D H) (batchSize f D H),
        |(f.cycleCount (rawRemainder f D H T.val):ℝ)-
          CandidateLogSurvival.zeta (unexposed f D H).card f.k (batchSize f D H)*
            f.cycleCount H| ≤
          (alpha N/100000)*(CandidateLogSurvival.zeta (unexposed f D H).card
            f.k (batchSize f D H)*f.cycleCount H) →
      let G := rawRemainder f D H T.val
      0<f.cycleCount G ∧ f.entropyBudget G (B+1) ∧
      Real.log N/4≤f.mu G ∧
      PathGraphUpperRegular r (4*C) L (f.numberedEdges (f.rawHost G)) ∧
      ∀ t : ℝ, 0<t → ((f.existingExceptional G t).card:ℝ)≤
        K*(f.m G:ℝ)/(t*Real.sqrt (Real.log (Real.log (N:ℝ)))) := by
  obtain ⟨K,hK,hstatic⟩ := Frame.remainder_existingExceptional_uniform_rate r hr (8*C) (B+1)
    (by positivity) (by linarith)
  refine ⟨K,hK,?_⟩
  filter_upwards [hstatic,inherited_remainder_regular_eventually r b hr C hC,
    inherited_restricted_budget_eventually r b hr C hC.le,
    eventually_frame_window_six r hr (4*C) L (by positivity) hL]
    with N hs hr' hb hw
  intro M ell original offset hadm f D hD j h c ω hh hMj hj hreg hbudget H T hsurv
  have hbg := hb M ell original offset hadm f D hD j h c L B ω hMj hj hreg hbudget T hsurv
  have hrg := hr' M ell original offset hadm f D hD j h c L ω hh hMj hj hreg T
  dsimp only
  refine ⟨hbg.1,hbg.2,hrg.1,hrg.2,?_⟩
  let G := rawRemainder f D H T.val
  have hregG : PathGraphUpperRegular r (8*C) 6 (f.entropyInstance G hbg.2.1).host := by
    have hh' := hw f G hbg.2.1 hrg.2
    convert hh' using 1 <;> ring
  let d : Frame.RemainderEntropyInput r (8*C) (B+1) N :=
    { original := original
      frame := f
      host := G
      budget := hbg.2
      markers_small := by simpa using hadm.markers_small
      density := hrg.1
      regular := hregG }
  exact hs d
end LooseHamilton.CandidateBalance
