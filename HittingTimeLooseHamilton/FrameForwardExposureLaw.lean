module

public import HittingTimeLooseHamilton.FrameForwardExposure

public section

noncomputable section
namespace LooseHamilton
open Finset FrameSurvival
variable {V : Type} [Fintype V] [DecidableEq V]

/-- The HostBatch law and the independent order law agree at a record's fixed
residual cardinality. This transports arbitrary forward witness predicates. -/
theorem hostBatch_event_record_size (H : SimpleHypergraph V) (m τ : ℕ)
    (hm : H.card=m) (hτ : τ ≤ m) (P : SimpleHypergraph V→Prop) :
    (FiniteEntropy.uniform : FiniteEntropy.Law (BatchOrder m)).event
      (fun σ=>P (batchSelection H m hm τ σ)) =
      (hostBatchLaw (show τ ≤ H.card by omega)).event (fun T=>P T.val) := by
  subst m
  exact selectedHostBatch_event H τ hτ P

lemma batchSelection_congr_host {H G : SimpleHypergraph V} (m τ : ℕ)
    (hH : H.card=m) (hG : G.card=m) (hHG : H=G) (σ : BatchOrder m) :
    batchSelection H m hH τ σ=batchSelection G m hG τ σ := by
  subst G
  rfl

namespace CandidateBalance
open AuxiliaryFrame
variable {r M : ℕ} {ell : V→ℕ} {original : Finset (Finset V)}

/-- Pointwise in every source of the exposure record, the observed removed
batch is the genuine uniform selection from its unexposed current graph. -/
theorem record_observed_batch [Nonempty (TerminalState V r M ell)]
    (f : Frame r original) (D : Finset V) (j : ℕ)
    (hMj : M ≤ j) (hj : j ≤ (completeEdges V r).card)
    (A0 B0 : SimpleHypergraph V)
    (hb : 0 < (extensionLaw r M ell).event
      (EdgeComplementEvent r M ell j (samplingUniverse f D) A0 B0))
    (τ : ℕ) (hτ : τ ≤ j-B0.card)
    (ω : Outcome V r M ell)
    (he : EdgeComplementEvent r M ell j (samplingUniverse f D) A0 B0 ω)
    (σ : BatchOrder (j-B0.card)) :
    (restrictedQBatchObserved r M ell j hMj hj (samplingUniverse f D) A0 B0
      (samplingUniverse_subset_complete f D) hb τ hτ (ω,σ)).val.2 =
    batchSelection (unexposed f D (extensionState ω.1 ω.2 j)) (j-B0.card)
      (record_unexposed_card f D j hMj hj A0 B0 ω he) τ σ := by
  letI := edgeComplement_nonempty r M ell j hMj hj (samplingUniverse f D) A0 B0
    (samplingUniverse_subset_complete f D) hb
  have hp := edgeComplementProjection_val r M ell j hMj hj (samplingUniverse f D) A0 B0 ω he
  change batchSelection (edgeComplementProjection r M ell j hMj hj
    (samplingUniverse f D) A0 B0 ω).val.2 (j-B0.card) _ τ σ = _
  exact batchSelection_congr_host _ _ _ _ (congrArg Prod.snd hp) σ

/-- HostBatch lower bounds transfer to the genuine recorded forward experiment,
for each source separately; no average over good sources is substituted. -/
theorem record_forward_event [Nonempty (TerminalState V r M ell)]
    (f : Frame r original) (D : Finset V) (j : ℕ)
    (hMj : M ≤ j) (hj : j ≤ (completeEdges V r).card)
    (A0 B0 : SimpleHypergraph V)
    (hb : 0 < (extensionLaw r M ell).event
      (EdgeComplementEvent r M ell j (samplingUniverse f D) A0 B0))
    (τ : ℕ) (hτ : τ ≤ j-B0.card)
    (ω : Outcome V r M ell)
    (he : EdgeComplementEvent r M ell j (samplingUniverse f D) A0 B0 ω)
    (P : SimpleHypergraph V→Prop) :
    (FiniteEntropy.uniform : FiniteEntropy.Law (BatchOrder (j-B0.card))).event
      (fun σ=>P (restrictedQBatchObserved r M ell j hMj hj (samplingUniverse f D) A0 B0
        (samplingUniverse_subset_complete f D) hb τ hτ (ω,σ)).val.2) =
    (hostBatchLaw (show τ ≤ (unexposed f D (extensionState ω.1 ω.2 j)).card by
      rw [record_unexposed_card f D j hMj hj A0 B0 ω he];exact hτ)).event (fun T=>P T.val) := by
  simp_rw [record_observed_batch f D j hMj hj A0 B0 hb τ hτ ω he]
  exact hostBatch_event_record_size _ _ _ _ hτ P
end CandidateBalance
end LooseHamilton
