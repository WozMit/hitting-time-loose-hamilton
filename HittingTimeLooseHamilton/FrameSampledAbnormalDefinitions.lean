module

public import HittingTimeLooseHamilton.FrameCandidateTransferActual

public section

/-! The actual sampled abnormal-role count in the retained-boundary experiment. -/
noncomputable section
namespace LooseHamilton.CandidateBalance
open Finset AuxiliaryFrame
variable {N r : ℕ} {original : Finset (Finset (Fin N))}

/-- Candidate roles carried by sampled edges and abnormal in the raw remainder. -/
@[expose] def sampledBadRoles (f : Frame r original) (D : Finset (Fin N))
    (H T : SimpleHypergraph (Fin N)) : Finset (Finset (Fin N) × Fin N × Fin N) := by
  classical
  exact f.candidates.filter (fun c => c.1 ∪ {c.2.1,c.2.2} ∈ T ∧
    FrameScales.alpha N/4 < |frameNormalizedCount f (rawRemainder f D H T) c-1|)

/-- The common main-survival indicator is outside the role count, not part
of a candidate-conditioned main-family concentration hypothesis. -/
@[expose] def mainSampledBadCount (f : Frame r original) (D : Finset (Fin N))
    (H T : SimpleHypergraph (Fin N)) : ℝ := by
  classical
  exact if MainCountSurvives f D H T then (sampledBadRoles f D H T).card else 0

lemma mainSampledBadCount_nonneg (f : Frame r original) (D : Finset (Fin N))
    (H T : SimpleHypergraph (Fin N)) : 0 ≤ mainSampledBadCount f D H T := by
  classical
  unfold mainSampledBadCount
  split_ifs <;> positivity

end LooseHamilton.CandidateBalance
