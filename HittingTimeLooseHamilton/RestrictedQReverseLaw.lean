module

public import HittingTimeLooseHamilton.RestrictedQBatchLaw

public section

/-! Item 30.4 in the actual complement-conditioned Q experiment.
These conclusions contain no assumed uniformity, witness, entropy or regularity
hypothesis. The only additional outer-law hypothesis is original no-deficit. -/
noncomputable section
namespace LooseHamilton
open Finset
variable {V : Type} [Fintype V] [DecidableEq V]
attribute [local instance] Classical.propDecidable

/-- Observation of both remainders after the independent residual-host batch. -/
@[expose] def restrictedQRemainderEvent (r M : ℕ) (ell : V → ℕ)
    [Nonempty (TerminalState V r M ell)] (j : ℕ) (hMj : M ≤ j)
    (hj : j ≤ (completeEdges V r).card)
    (U A0 B0 : SimpleHypergraph V) (hU : U ⊆ completeEdges V r)
    (hb : 0 < (extensionLaw r M ell).event (EdgeComplementEvent r M ell j U A0 B0))
    (τ : ℕ) (hτ : τ ≤ j-B0.card) (F F0 : SimpleHypergraph V)
    (ω : (TerminalState V r M ell × MissingOrder V r M) × BatchOrder (j-B0.card)) : Prop :=
  let b := restrictedQBatchObserved r M ell j hMj hj U A0 B0 hU hb τ hτ ω
  b.val.1.val.2 \ b.val.2 = F ∧ b.val.1.val.1 \ b.val.2 = F0

/-- Exact reverse pair law including terminal feasibility. The removed terminal
size is M-|A0|-|F0|. No replacement of Q by a static lower-bound law is made. -/
theorem restrictedQ_reverse_pair_law (r M : ℕ) (ell : V → ℕ)
    [Nonempty (TerminalState V r M ell)] (j : ℕ) (hMj : M ≤ j)
    (hj : j ≤ (completeEdges V r).card)
    (U A0 B0 : SimpleHypergraph V) (hU : U ⊆ completeEdges V r)
    (hb : 0 < (extensionLaw r M ell).event (EdgeComplementEvent r M ell j U A0 B0))
    (τ : ℕ) (hτ : τ ≤ j-B0.card) (F F0 : SimpleHypergraph V)
    (hE : 0 < (restrictedQBatchLaw r M ell j U A0 B0 hb).event
      (restrictedQRemainderEvent r M ell j hMj hj U A0 B0 hU hb τ hτ F F0)) :
    ∃ hR : Nonempty (RestrictedReverseState U A0 F F0 ell (M-A0.card) τ),
    ∀ P : SimpleHypergraph V × SimpleHypergraph V → Prop,
      ((restrictedQBatchLaw r M ell j U A0 B0 hb).condition
        (restrictedQRemainderEvent r M ell j hMj hj U A0 B0 hU hb τ hτ F F0) hE).event
        (fun ω => let b := restrictedQBatchObserved r M ell j hMj hj U A0 B0 hU hb τ hτ ω
          P (b.val.2 ∩ b.val.1.val.1, b.val.2)) =
      (@FiniteEntropy.uniform (RestrictedReverseState U A0 F F0 ell (M-A0.card) τ)
        inferInstance hR).event (fun q => P q.val) := by
  letI := restrictedQBatch_nonempty r M ell j hMj hj U A0 B0 hU hb τ hτ
  exact restrictedReverse_pair_law_of_uniform_pushforward U A0 F F0 ell
    (M-A0.card) (j-B0.card) τ (restrictedQBatchLaw r M ell j U A0 B0 hb)
    (restrictedQBatchObserved r M ell j hMj hj U A0 B0 hU hb τ hτ)
    (restrictedQBatch_uniform r M ell j hMj hj U A0 B0 hU hb τ hτ) hE

/-- Item 30.4: conditional on an attainable fixed complement and both remainders,
if A0 union F0 meets the ORIGINAL lower bounds, the removed batch is precisely
uniform among all tau-subsets of U minus F. No bounded adjusted-offset condition
is imposed, and F0 is allowed to have fewer than M-|A0| edges. -/
theorem restrictedQ_reverse_batch_law (r M : ℕ) (ell : V → ℕ)
    [Nonempty (TerminalState V r M ell)] (j : ℕ) (hMj : M ≤ j)
    (hj : j ≤ (completeEdges V r).card)
    (U A0 B0 : SimpleHypergraph V) (hU : U ⊆ completeEdges V r)
    (hb : 0 < (extensionLaw r M ell).event (EdgeComplementEvent r M ell j U A0 B0))
    (τ : ℕ) (hτ : τ ≤ j-B0.card) (F F0 : SimpleHypergraph V)
    (h0 : ∀ v, ell v ≤ vertexDegree (A0 ∪ F0) v)
    (hE : 0 < (restrictedQBatchLaw r M ell j U A0 B0 hb).event
      (restrictedQRemainderEvent r M ell j hMj hj U A0 B0 hU hb τ hτ F F0)) :
    ∃ hT : Nonempty ↥((U \ F).powersetCard τ),
    ∀ P : SimpleHypergraph V → Prop,
      ((restrictedQBatchLaw r M ell j U A0 B0 hb).condition
        (restrictedQRemainderEvent r M ell j hMj hj U A0 B0 hU hb τ hτ F F0) hE).event
        (fun ω => P (restrictedQBatchObserved r M ell j hMj hj U A0 B0 hU hb τ hτ ω).val.2) =
      (@FiniteEntropy.uniform ↥((U \ F).powersetCard τ) inferInstance hT).event
        (fun T => P T.val) := by
  letI := restrictedQBatch_nonempty r M ell j hMj hj U A0 B0 hU hb τ hτ
  exact restrictedReverse_batch_law_of_uniform_pushforward U A0 F F0 ell
    (M-A0.card) (j-B0.card) τ (restrictedQBatchLaw r M ell j U A0 B0 hb)
    (restrictedQBatchObserved r M ell j hMj hj U A0 B0 hU hb τ hτ)
    (restrictedQBatch_uniform r M ell j hMj hj U A0 B0 hU hb τ hτ) h0 hE

end LooseHamilton
