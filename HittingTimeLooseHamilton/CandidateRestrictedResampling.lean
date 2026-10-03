module

public import HittingTimeLooseHamilton.RestrictedQReverseLaw
public import HittingTimeLooseHamilton.EdgeComplementBoundary

public section

/-! Direct application of items 30.3–30.4 to the exact frame universe from 30.2.
No boundary vertex is required to have been deleted from the active frame. -/
noncomputable section
namespace LooseHamilton.CandidateBalance
open Finset AuxiliaryFrame
variable {V : Type} [Fintype V] [DecidableEq V]
variable {r : ℕ} {original : Finset (Finset V)}

/-- The residual pair law for the original-prohibition frame universe. -/
theorem frame_complement_pair_law (M : ℕ) (ell : V → ℕ)
    [Nonempty (TerminalState V r M ell)] (j : ℕ) (hMj : M ≤ j)
    (hj : j ≤ (completeEdges V r).card) (f : Frame r original) (D : Finset V)
    (A0 B0 : SimpleHypergraph V)
    (hb : 0 < (extensionLaw r M ell).event
      (EdgeComplementEvent r M ell j (samplingUniverse f D) A0 B0)) :
    ∃ hne : Nonempty (EdgeComplementPair (samplingUniverse f D) A0 ell (M-A0.card) (j-B0.card)),
    ∀ P : SimpleHypergraph V × SimpleHypergraph V → Prop,
      ((extensionLaw r M ell).condition
        (EdgeComplementEvent r M ell j (samplingUniverse f D) A0 B0) hb).event
        (fun ω => P (unexposed f D ω.1.val, unexposed f D (extensionState ω.1 ω.2 j))) =
      (@FiniteEntropy.uniform
        (EdgeComplementPair (samplingUniverse f D) A0 ell (M-A0.card) (j-B0.card))
        inferInstance hne).event (fun p => P p.val) := by
  exact edgeComplement_conditional_uniform r M ell j hMj hj
    (samplingUniverse f D) A0 B0 (samplingUniverse_subset_complete f D) hb

/-- The final exact reverse law for this frame's unexposed allowed edges.
The original terminal degree constraints retain A0; the missing-edge universe
is U minus the UNEXPOSED remainder F, not the full raw frame host. -/
theorem frame_restricted_reverse_batch_law (M : ℕ) (ell : V → ℕ)
    [Nonempty (TerminalState V r M ell)] (j : ℕ) (hMj : M ≤ j)
    (hj : j ≤ (completeEdges V r).card) (f : Frame r original) (D : Finset V)
    (A0 B0 : SimpleHypergraph V)
    (hb : 0 < (extensionLaw r M ell).event
      (EdgeComplementEvent r M ell j (samplingUniverse f D) A0 B0))
    (τ : ℕ) (hτ : τ ≤ j-B0.card) (F F0 : SimpleHypergraph V)
    (h0 : ∀ v, ell v ≤ vertexDegree (A0 ∪ F0) v)
    (hE : 0 < (restrictedQBatchLaw r M ell j (samplingUniverse f D) A0 B0 hb).event
      (restrictedQRemainderEvent r M ell j hMj hj (samplingUniverse f D) A0 B0
        (samplingUniverse_subset_complete f D) hb τ hτ F F0)) :
    ∃ hT : Nonempty ↥(((samplingUniverse f D) \ F).powersetCard τ),
    ∀ P : SimpleHypergraph V → Prop,
      ((restrictedQBatchLaw r M ell j (samplingUniverse f D) A0 B0 hb).condition
        (restrictedQRemainderEvent r M ell j hMj hj (samplingUniverse f D) A0 B0
          (samplingUniverse_subset_complete f D) hb τ hτ F F0) hE).event
        (fun ω => P (restrictedQBatchObserved r M ell j hMj hj (samplingUniverse f D) A0 B0
          (samplingUniverse_subset_complete f D) hb τ hτ ω).val.2) =
      (@FiniteEntropy.uniform ↥(((samplingUniverse f D) \ F).powersetCard τ)
        inferInstance hT).event (fun T => P T.val) := by
  exact restrictedQ_reverse_batch_law r M ell j hMj hj
    (samplingUniverse f D) A0 B0 (samplingUniverse_subset_complete f D) hb τ hτ F F0 h0 hE

end LooseHamilton.CandidateBalance
