module

public import HittingTimeLooseHamilton.FrameRecordCandidateBound
public import HittingTimeLooseHamilton.FrameSamplingParameters

public section

noncomputable section
namespace LooseHamilton.CandidateBalance
open Finset AuxiliaryFrame FrameSurvival Filter FrameScales Topology

/-- The exact exponential estimate in each positive-probability complement
record; regularity, entropy budget and badness remain inside the event. -/
@[expose] def RecordExponentialBound (r b : ℕ) (C B L offset : ℝ) (N : ℕ) (rate : ℝ) : Prop :=
  ∀ (M : ℕ) (ell : Fin N → ℕ) (original : Finset (Finset (Fin N))),
  ∀ hadm : CoreAdmissible r M ell original offset,
  letI := hadm.feasible
  ∀ (f : Frame r original) (D : Finset (Fin N)), D.card≤b →
  ∀ (j h : ℕ) (c : ℝ), 4*r≤h →
  ∀ (hMj : M≤j) (hj : j≤(completeEdges (Fin N) r).card),
  ∀ (A0 B0 : SimpleHypergraph (Fin N)),
  ∀ hb : 0<(extensionLaw r M ell).event
    (EdgeComplementEvent r M ell j (samplingUniverse f D) A0 B0),
    ((extensionLaw r M ell).condition
      (EdgeComplementEvent r M ell j (samplingUniverse f D) A0 B0) hb).event
      (BadSource f j h c C L B)≤errorBound N rate

/-- Only a factor two is lost on removing the common forward-error factor. -/
lemma remove_forward_error {p err x : ℝ} (hp : 0≤p) (he : err≤1/2)
    (hb : (1-err)*p≤Real.exp x) : p≤2*Real.exp x := by
  have hm := mul_le_mul_of_nonneg_right (show (1/2:ℝ)≤1-err by linarith) hp
  linarith
end LooseHamilton.CandidateBalance
