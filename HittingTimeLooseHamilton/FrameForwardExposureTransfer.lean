module

public import HittingTimeLooseHamilton.FrameForwardExposureWitness

public section

noncomputable section
namespace LooseHamilton.CandidateBalance
open Finset AuxiliaryFrame FrameSurvival
variable {N r M : ℕ} {ell : Fin N→ℕ} {original : Finset (Finset (Fin N))}

/-- Witness predicate on the exact uniform restricted triple used by reverse sampling. -/
@[expose] def recordForwardEvent (f : Frame r original) (D : Finset (Fin N))
    (A0 B0 : SimpleHypergraph (Fin N)) (ell : Fin N→ℕ) (s t τ : ℕ)
    (b : RestrictedBatchState (samplingUniverse f D) A0 ell s t τ) : Prop :=
  RecordForwardWitnessSuccess f D A0 B0 ell τ
    (b.val.1.val.2\b.val.2) (b.val.1.val.1\b.val.2) b.val.2

theorem record_forward_lower_transfer [Nonempty (TerminalState (Fin N) r M ell)]
    (f : Frame r original) (D : Finset (Fin N)) (j : ℕ)
    (hMj : M ≤ j) (hj : j ≤ (completeEdges (Fin N) r).card)
    (A0 B0 : SimpleHypergraph (Fin N))
    (hb : 0 < (extensionLaw r M ell).event
      (EdgeComplementEvent r M ell j (samplingUniverse f D) A0 B0))
    (hτ : recordBatchSize f j B0 ≤ j-B0.card)
    (ω : Outcome (Fin N) r M ell)
    (he : EdgeComplementEvent r M ell j (samplingUniverse f D) A0 B0 ω)
    (ε : ℝ)
    (hforward : 1-ε ≤
      (hostBatchLaw (show recordBatchSize f j B0 ≤
        (unexposed f D (extensionState ω.1 ω.2 j)).card by
          rw [record_unexposed_card f D j hMj hj A0 B0 ω he];exact hτ)).event
        (fun T => ForwardWitnessSuccess f D ω.1.val ell (extensionState ω.1 ω.2 j) T.val)) :
    1-ε ≤ (FiniteEntropy.uniform : FiniteEntropy.Law (BatchOrder (j-B0.card))).event
      (fun σ => recordForwardEvent f D A0 B0 ell (M-A0.card) (j-B0.card) (recordBatchSize f j B0)
        (restrictedQBatchObserved r M ell j hMj hj (samplingUniverse f D) A0 B0
          (samplingUniverse_subset_complete f D) hb (recordBatchSize f j B0) hτ (ω,σ))) := by
  have hsource := record_forward_event f D j hMj hj A0 B0 hb
    (recordBatchSize f j B0) hτ ω he
    (ForwardWitnessSuccess f D ω.1.val ell (extensionState ω.1 ω.2 j))
  rw [←hsource] at hforward
  apply hforward.trans
  apply FiniteEntropy.Law.event_mono
  intro σ hs
  let b := restrictedQBatchObserved r M ell j hMj hj (samplingUniverse f D) A0 B0
    (samplingUniverse_subset_complete f D) hb (recordBatchSize f j B0) hτ (ω,σ)
  have hv := restrictedQBatch_pair_values r M ell j hMj hj (samplingUniverse f D) A0 B0
    (samplingUniverse_subset_complete f D) hb (recordBatchSize f j B0) hτ (ω,σ) he
  have ht : b.val.2⊆unexposed f D (extensionState ω.1 ω.2 j) := by
    have hh := b.property.1
    change b.val.1.val = _ at hv
    have hp := congrArg Prod.snd hv
    rw [hp] at hh
    exact hh
  have hh := (record_forward_witness_iff f D j hMj hj A0 B0 b.val.2 ω he ht).mp hs
  change recordForwardEvent f D A0 B0 ell _ _ _ b
  unfold recordForwardEvent
  change b.val.1.val = _ at hv
  have hv₁ := congrArg Prod.fst hv
  have hv₂ := congrArg Prod.snd hv
  rw [hv₁,hv₂]
  exact hh
end LooseHamilton.CandidateBalance
