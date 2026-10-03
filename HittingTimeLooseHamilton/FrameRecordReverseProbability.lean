module

public import HittingTimeLooseHamilton.FrameRecordReverseFibers
public import HittingTimeLooseHamilton.FrameReverseWitnessTail

public section

noncomputable section
namespace LooseHamilton.CandidateBalance
open Finset AuxiliaryFrame FrameScales
variable {N r : ℕ} {original : Finset (Finset (Fin N))}

/-- The complete reverse estimate on the uniform restricted triple. All
nonadmissible remainder fibres contribute zero witness probability. -/
theorem record_reverse_uniform_bound (f : Frame r original) (D : Finset (Fin N))
    (A0 B0 : SimpleHypergraph (Fin N)) (ell : Fin N→ℕ) (s t τ : ℕ)
    [Nonempty (RestrictedBatchState (samplingUniverse f D) A0 ell s t τ)]
    (hα : 0≤alpha N) (hsmall : alpha N≤1/16) :
    (FiniteEntropy.uniform : FiniteEntropy.Law
      (RestrictedBatchState (samplingUniverse f D) A0 ell s t τ)).event
      (recordForwardEvent f D A0 B0 ell s t τ) ≤ Real.exp (-alpha N*τ/64) := by
  apply record_reverse_event_le f D A0 B0 ell s t τ
  intro F F0 hR
  letI := hR
  exact record_reverse_witness_tail f D A0 B0 F F0 ell s τ hα hsmall

/-- Push the unconditional reverse estimate back to the actual complement-
conditioned Q source followed by its independent residual-host batch.
Regularity, entropy and candidate badness are not conditioning events. -/
theorem record_reverse_q_event_bound (M : ℕ) (ell : Fin N→ℕ)
    [Nonempty (TerminalState (Fin N) r M ell)]
    (f : Frame r original) (D : Finset (Fin N)) (j : ℕ)
    (hMj : M≤j) (hj : j≤(completeEdges (Fin N) r).card)
    (A0 B0 : SimpleHypergraph (Fin N))
    (hb : 0<(extensionLaw r M ell).event
      (EdgeComplementEvent r M ell j (samplingUniverse f D) A0 B0))
    (τ : ℕ) (hτ : τ≤j-B0.card) (hα : 0≤alpha N) (hsmall : alpha N≤1/16) :
    (restrictedQBatchLaw r M ell j (samplingUniverse f D) A0 B0 hb).event
      (fun ω => recordForwardEvent f D A0 B0 ell (M-A0.card) (j-B0.card) τ
        (restrictedQBatchObserved r M ell j hMj hj (samplingUniverse f D) A0 B0
          (samplingUniverse_subset_complete f D) hb τ hτ ω)) ≤ Real.exp (-alpha N*τ/64) := by
  letI := restrictedQBatch_nonempty r M ell j hMj hj (samplingUniverse f D) A0 B0
    (samplingUniverse_subset_complete f D) hb τ hτ
  have hu := restrictedQBatch_uniform r M ell j hMj hj (samplingUniverse f D) A0 B0
    (samplingUniverse_subset_complete f D) hb τ hτ
  rw [←FiniteEntropy.Law.event_map,hu]
  exact record_reverse_uniform_bound f D A0 B0 ell (M-A0.card) (j-B0.card) τ hα hsmall
end LooseHamilton.CandidateBalance
