module

public import HittingTimeLooseHamilton.FrameCandidateTransferActual
public import HittingTimeLooseHamilton.UnstableFraction

public section

/-! Large-completion failures normalized by all legal candidates. -/
noncomputable section
namespace LooseHamilton.CandidateBalance
open Finset AuxiliaryFrame FrameScales
attribute [local instance] Classical.propDecidable
variable {N r : ℕ} {original : Finset (Finset (Fin N))}

/-- Only legal, large source completions can be unstable in this predicate. -/
@[expose] def LargeCompletionUnstable (f : Frame r original) (D : Finset (Fin N))
    (H : SimpleHypergraph (Fin N)) (a : Finset (Fin N) × Fin N × Fin N)
    (T : SimpleHypergraph (Fin N)) : Prop :=
  f.LegalCandidate a ∧
  (f.cycleCount H:ℝ)*(N:ℝ)^(-(100*(r:ℝ))) ≤ f.completionCount H a ∧
  ¬CompletionCountSurvives f D H T a
    (CandidateLogSurvival.zeta (unexposed f D H).card (f.k-1) (batchSize f D H))

/-- The denominator is the entire legal candidate set, including tiny ones. -/
@[expose] def largeCompletionUnstableFraction (f : Frame r original) (D : Finset (Fin N))
    (H T : SimpleHypergraph (Fin N)) : ℝ :=
  FiniteEntropy.Law.unstableFraction f.candidates
    (fun a T => LargeCompletionUnstable f D H a T) T

lemma largeCompletionUnstableFraction_eq (f : Frame r original) (D : Finset (Fin N))
    (H T : SimpleHypergraph (Fin N)) :
    largeCompletionUnstableFraction f D H T =
      ((f.candidates.filter (fun a => LargeCompletionUnstable f D H a T)).card:ℝ)/
        f.candidates.card := rfl

end LooseHamilton.CandidateBalance
