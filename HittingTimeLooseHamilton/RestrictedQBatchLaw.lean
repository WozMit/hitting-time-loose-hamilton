module

public import HittingTimeLooseHamilton.EdgeComplementProjection
public import HittingTimeLooseHamilton.RestrictedBatchSampling
public import HittingTimeLooseHamilton.RestrictedReverseConditional

public section

/-! The restricted reverse experiment starts with the actual Q path conditioned
on its fixed complement record, then samples an independent uniform batch. -/
noncomputable section
namespace LooseHamilton
open Finset
variable {V : Type} [Fintype V] [DecidableEq V]
attribute [local instance] Classical.propDecidable

lemma edgeComplement_nonempty (r M : ℕ) (ell : V → ℕ)
    [Nonempty (TerminalState V r M ell)] (j : ℕ) (hMj : M ≤ j)
    (hj : j ≤ (completeEdges V r).card)
    (U A0 B0 : SimpleHypergraph V) (hU : U ⊆ completeEdges V r)
    (hb : 0 < (extensionLaw r M ell).event (EdgeComplementEvent r M ell j U A0 B0)) :
    Nonempty (EdgeComplementPair U A0 ell (M-A0.card) (j-B0.card)) := by
  obtain ⟨hne,_⟩ := edgeComplement_conditional_uniform r M ell j hMj hj U A0 B0 hU hb
  exact hne

/-- The independent random order has the residual current size j-|B0|,
not the raw frame size. Its prefix selects a uniform batch of residual edges. -/
@[expose] def restrictedQBatchLaw (r M : ℕ) (ell : V → ℕ)
    [Nonempty (TerminalState V r M ell)] (j : ℕ) (U A0 B0 : SimpleHypergraph V)
    (hb : 0 < (extensionLaw r M ell).event (EdgeComplementEvent r M ell j U A0 B0)) :
    FiniteEntropy.Law ((TerminalState V r M ell × MissingOrder V r M) × BatchOrder (j-B0.card)) :=
  ((extensionLaw r M ell).condition (EdgeComplementEvent r M ell j U A0 B0) hb).prod
    FiniteEntropy.uniform

@[expose] def restrictedQBatchObserved (r M : ℕ) (ell : V → ℕ)
    [Nonempty (TerminalState V r M ell)] (j : ℕ) (hMj : M ≤ j)
    (hj : j ≤ (completeEdges V r).card)
    (U A0 B0 : SimpleHypergraph V) (hU : U ⊆ completeEdges V r)
    (hb : 0 < (extensionLaw r M ell).event (EdgeComplementEvent r M ell j U A0 B0))
    (τ : ℕ) (hτ : τ ≤ j-B0.card)
    (ω : (TerminalState V r M ell × MissingOrder V r M) × BatchOrder (j-B0.card)) :
    RestrictedBatchState U A0 ell (M-A0.card) (j-B0.card) τ := by
  letI := edgeComplement_nonempty r M ell j hMj hj U A0 B0 hU hb
  exact RestrictedSampling.observe
    (fun p : EdgeComplementPair U A0 ell (M-A0.card) (j-B0.card) => p.val.2)
    (j-B0.card) τ (fun p => p.property.2.2.2.1) hτ
    (edgeComplementProjection r M ell j hMj hj U A0 B0) ω

lemma restrictedQBatch_nonempty (r M : ℕ) (ell : V → ℕ)
    [Nonempty (TerminalState V r M ell)] (j : ℕ) (hMj : M ≤ j)
    (hj : j ≤ (completeEdges V r).card)
    (U A0 B0 : SimpleHypergraph V) (hU : U ⊆ completeEdges V r)
    (hb : 0 < (extensionLaw r M ell).event (EdgeComplementEvent r M ell j U A0 B0))
    (τ : ℕ) (hτ : τ ≤ j-B0.card) :
    Nonempty (RestrictedBatchState U A0 ell (M-A0.card) (j-B0.card) τ) := by
  letI := edgeComplement_nonempty r M ell j hMj hj U A0 B0 hU hb
  exact RestrictedSampling.state_nonempty
    (fun p : EdgeComplementPair U A0 ell (M-A0.card) (j-B0.card) => p.val.2)
    (j-B0.card) τ (fun p => p.property.2.2.2.1) hτ

/-- Exact uniform triple law, derived from item 30.3 and fresh independent
sampling. It is a theorem about Q, not a uniformity hypothesis. -/
theorem restrictedQBatch_uniform (r M : ℕ) (ell : V → ℕ)
    [Nonempty (TerminalState V r M ell)] (j : ℕ) (hMj : M ≤ j)
    (hj : j ≤ (completeEdges V r).card)
    (U A0 B0 : SimpleHypergraph V) (hU : U ⊆ completeEdges V r)
    (hb : 0 < (extensionLaw r M ell).event (EdgeComplementEvent r M ell j U A0 B0))
    (τ : ℕ) (hτ : τ ≤ j-B0.card) :
    (restrictedQBatchLaw r M ell j U A0 B0 hb).map
      (restrictedQBatchObserved r M ell j hMj hj U A0 B0 hU hb τ hτ) =
    @FiniteEntropy.uniform (RestrictedBatchState U A0 ell (M-A0.card) (j-B0.card) τ)
      inferInstance (restrictedQBatch_nonempty r M ell j hMj hj U A0 B0 hU hb τ hτ) := by
  letI := edgeComplement_nonempty r M ell j hMj hj U A0 B0 hU hb
  exact RestrictedSampling.observed_law_uniform
    ((extensionLaw r M ell).condition (EdgeComplementEvent r M ell j U A0 B0) hb)
    (edgeComplementProjection r M ell j hMj hj U A0 B0)
    (edgeComplement_projection_uniform r M ell j hMj hj U A0 B0 hU hb)
    (fun p : EdgeComplementPair U A0 ell (M-A0.card) (j-B0.card) => p.val.2)
    (j-B0.card) τ (fun p => p.property.2.2.2.1) hτ

/-- On the positive-probability exposure event the observed terminal/current
components are exactly the restrictions of the original Q graphs. -/
theorem restrictedQBatch_pair_values (r M : ℕ) (ell : V → ℕ)
    [Nonempty (TerminalState V r M ell)] (j : ℕ) (hMj : M ≤ j)
    (hj : j ≤ (completeEdges V r).card)
    (U A0 B0 : SimpleHypergraph V) (hU : U ⊆ completeEdges V r)
    (hb : 0 < (extensionLaw r M ell).event (EdgeComplementEvent r M ell j U A0 B0))
    (τ : ℕ) (hτ : τ ≤ j-B0.card)
    (ω : (TerminalState V r M ell × MissingOrder V r M) × BatchOrder (j-B0.card))
    (he : EdgeComplementEvent r M ell j U A0 B0 ω.1) :
    (restrictedQBatchObserved r M ell j hMj hj U A0 B0 hU hb τ hτ ω).val.1.val =
      (ω.1.1.val ∩ U, extensionState ω.1.1 ω.1.2 j ∩ U) := by
  letI := edgeComplement_nonempty r M ell j hMj hj U A0 B0 hU hb
  exact edgeComplementProjection_val r M ell j hMj hj U A0 B0 ω.1 he

end LooseHamilton
