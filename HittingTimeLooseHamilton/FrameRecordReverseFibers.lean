module

public import HittingTimeLooseHamilton.FrameForwardExposureTransfer
public import HittingTimeLooseHamilton.RootConditionalMixture

public section

noncomputable section
namespace LooseHamilton.CandidateBalance
open Finset AuxiliaryFrame
variable {N r : ℕ} {original : Finset (Finset (Fin N))}

/-- Exact conditional witness law in an attainable pair of remainders.
The forward event is rewritten using the two remainder values before transport. -/
theorem record_reverse_fiber_event (f : Frame r original) (D : Finset (Fin N))
    (A0 B0 F F0 : SimpleHypergraph (Fin N)) (ell : Fin N→ℕ) (s t τ : ℕ)
    [Nonempty (RestrictedBatchState (samplingUniverse f D) A0 ell s t τ)]
    (hE : 0 < (FiniteEntropy.uniform : FiniteEntropy.Law
      (RestrictedBatchState (samplingUniverse f D) A0 ell s t τ)).event
        (fun b => b.val.1.val.2\b.val.2=F ∧ b.val.1.val.1\b.val.2=F0)) :
    ∃ hR : Nonempty (RestrictedReverseState (samplingUniverse f D) A0 F F0 ell s τ),
    ((FiniteEntropy.uniform : FiniteEntropy.Law
      (RestrictedBatchState (samplingUniverse f D) A0 ell s t τ)).condition
        (fun b => b.val.1.val.2\b.val.2=F ∧ b.val.1.val.1\b.val.2=F0) hE).event
      (recordForwardEvent f D A0 B0 ell s t τ) =
    (@FiniteEntropy.uniform (RestrictedReverseState (samplingUniverse f D) A0 F F0 ell s τ)
      inferInstance hR).event
        (fun p => RecordForwardWitnessSuccess f D A0 B0 ell τ F F0 p.val.2) := by
  classical
  obtain ⟨b,hb⟩ := exists_of_event_pos _ _ hE
  let W : RestrictedReverseFiber (samplingUniverse f D) A0 F F0 ell s t τ := ⟨b,hb⟩
  let e := restrictedReverseEquiv (samplingUniverse f D) A0 F F0 ell s t τ W
  letI : Nonempty (RestrictedReverseFiber (samplingUniverse f D) A0 F F0 ell s t τ) := ⟨W⟩
  letI : Nonempty (RestrictedReverseState (samplingUniverse f D) A0 F F0 ell s τ) := ⟨e W⟩
  refine ⟨inferInstance,?_⟩
  apply uniform_conditioned_equiv _ _ e _ _ hE
  intro z
  change RecordForwardWitnessSuccess f D A0 B0 ell τ
    (z.val.val.1.val.2\z.val.val.2) (z.val.val.1.val.1\z.val.val.2) z.val.val.2 ↔ _
  rw [z.property.1,z.property.2]
  rfl

/-- Average the proved reverse bounds over all attainable remainder pairs.
No regularity, entropy, or source-badness condition is imposed on this law. -/
theorem record_reverse_event_le (f : Frame r original) (D : Finset (Fin N))
    (A0 B0 : SimpleHypergraph (Fin N)) (ell : Fin N→ℕ) (s t τ : ℕ)
    [Nonempty (RestrictedBatchState (samplingUniverse f D) A0 ell s t τ)]
    (q : ℝ)
    (hbound : ∀ F F0 : SimpleHypergraph (Fin N),
      ∀ hR : Nonempty (RestrictedReverseState (samplingUniverse f D) A0 F F0 ell s τ),
      (@FiniteEntropy.uniform (RestrictedReverseState (samplingUniverse f D) A0 F F0 ell s τ)
        inferInstance hR).event
        (fun p => RecordForwardWitnessSuccess f D A0 B0 ell τ F F0 p.val.2) ≤ q) :
    (FiniteEntropy.uniform : FiniteEntropy.Law
      (RestrictedBatchState (samplingUniverse f D) A0 ell s t τ)).event
      (recordForwardEvent f D A0 B0 ell s t τ) ≤ q := by
  apply event_le_of_observation_conditional_bounds _ _
    (fun b => (b.val.1.val.2\b.val.2,b.val.1.val.1\b.val.2)) q
  rintro ⟨F,F0⟩ hF
  simp only [Prod.mk.injEq] at hF ⊢
  obtain ⟨hR,he⟩ := record_reverse_fiber_event f D A0 B0 F F0 ell s t τ hF
  rw [he]
  exact hbound F F0 hR
end LooseHamilton.CandidateBalance
