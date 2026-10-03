module

public import HittingTimeLooseHamilton.FrameReverseWitnessTailScalar
public import HittingTimeLooseHamilton.FrameForwardExposureWitness
public import HittingTimeLooseHamilton.RestrictedReverseUniform

public section

noncomputable section
namespace LooseHamilton.CandidateBalance
open Finset AuxiliaryFrame FrameScales
variable {N r : ℕ} {original : Finset (Finset (Fin N))}

/-- Conditional reverse witness bound at fixed current and terminal remainders.
If terminal feasibility or density fails, the witness event is empty; otherwise
cached reverse uniformity and the genuine hypergeometric tail apply. -/
theorem record_reverse_witness_tail (f : Frame r original) (D : Finset (Fin N))
    (A0 B0 F F0 : SimpleHypergraph (Fin N)) (ell : Fin N→ℕ) (s τ : ℕ)
    [Nonempty (RestrictedReverseState (samplingUniverse f D) A0 F F0 ell s τ)]
    (hα : 0≤alpha N) (hsmall : alpha N≤1/16) :
    (FiniteEntropy.uniform : FiniteEntropy.Law
      (RestrictedReverseState (samplingUniverse f D) A0 F F0 ell s τ)).event
      (fun p => RecordForwardWitnessSuccess f D A0 B0 ell τ F F0 p.val.2) ≤
        Real.exp (-alpha N*τ/64) := by
  classical
  let U := samplingUniverse f D
  let E := missingAbnormalEdges f D (F∪(B0∩allowedUniverse f))
  by_cases hgood : (∀v,ell v≤vertexDegree (A0∪F0) v) ∧
      E⊆U\F ∧ 0<(U\F).card ∧ alpha N/8*((U\F).card:ℝ)≤E.card
  · letI := restrictedReverse_outer_nonempty U A0 F F0 ell s τ
    have hτ : τ≤(U\F).card := by
      obtain ⟨T⟩ := (inferInstance : Nonempty ↥((U\F).powersetCard τ))
      have hh := mem_powersetCard.mp T.property
      exact hh.2 ▸ card_le_card hh.1
    have ht := frame_reverse_uniform_tail (U\F) E hgood.2.1 τ hτ hgood.2.2.1
      hα hsmall hgood.2.2.2
    have he := restrictedReverse_outer_uniform_event U A0 F F0 ell s τ hgood.1
      (fun T => ((T∩E).card:ℝ)≤(alpha N)^2*τ)
    apply le_trans _ (he.symm ▸ ht)
    apply FiniteEntropy.Law.event_mono
    intro p hp
    exact hp.2.2.2.2
  · have he : (FiniteEntropy.uniform : FiniteEntropy.Law
        (RestrictedReverseState U A0 F F0 ell s τ)).event
        (fun p => RecordForwardWitnessSuccess f D A0 B0 ell τ F F0 p.val.2)=0 := by
      apply FiniteEntropy.Law.event_eq_zero_of_false
      intro p hp
      exact hgood ⟨hp.1,hp.2.1,hp.2.2.1,hp.2.2.2.1⟩
    rw [he]
    exact (Real.exp_pos _).le
end LooseHamilton.CandidateBalance
