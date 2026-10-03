module

public import HittingTimeLooseHamilton.FrameForwardWitnessUniform

public section

noncomputable section
namespace LooseHamilton.CandidateBalance
open Finset AuxiliaryFrame FrameSurvival Filter FrameScales Topology

/-- The full pointwise forward claim at one original size and one common error. -/
@[expose] def PointwiseForwardBound (r b : ℕ) (C B L offset : ℝ) (N : ℕ) (err : ℝ) : Prop :=
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
      1-err ≤ (hostBatchLaw hτ).event
        (fun T => ForwardWitnessSuccess f D ω.1.val ell H T.val)

/-- Item 30.16: one vanishing error, chosen before every frame, source, time
and fixed bounded-boundary record. The forward claim has no unproved
concentration, overlap or forward-witness premise. -/
theorem pointwise_forward_witness (r b : ℕ) (hr : 3 ≤ r)
    (C B L offset : ℝ) (hC : 0 < C) (hB : 0 ≤ B) (hL : 0 < L) :
    ∃ err : ℕ → ℝ, Tendsto err atTop (nhds 0) ∧
      ∀ᶠ N : ℕ in atTop, 0 ≤ err N ∧ err N < 1 ∧
        PointwiseForwardBound r b C B L offset N (err N) := by
  obtain ⟨Km,Kc,Kg,hKm,hKc,hKg,hforward⟩ :=
    inherited_forward_witness_eventually r b hr C B L offset hC hB hL
  refine ⟨forwardError r C Km Kc Kg,
    forwardError_tendsto_zero (by omega) hC.le hKm.le hKc.le, ?_⟩
  filter_upwards [hforward,
    forwardError_eventually_nonneg (r := r) (by omega) hC.le hKm.le hKc.le hKg.le,
    eventually_forwardError_lt_one (r := r) (Kg := Kg) (by omega) hC.le hKm.le hKc.le]
    with N hf hnonneg hsmall
  exact ⟨hnonneg,hsmall,hf⟩

end LooseHamilton.CandidateBalance
