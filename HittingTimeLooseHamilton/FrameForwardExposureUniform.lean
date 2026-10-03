module

public import HittingTimeLooseHamilton.FrameForwardExposureTransfer
public import HittingTimeLooseHamilton.FrameForwardWitnessUniform

public section

noncomputable section
namespace LooseHamilton.CandidateBalance
open Finset AuxiliaryFrame FrameSurvival Filter FrameScales

lemma hostBatch_event_size_eq {α : Type*} [DecidableEq α] (H : Finset α)
    (τ τ' : ℕ) (he : τ=τ') (hτ : τ≤H.card) (hτ' : τ'≤H.card)
    (P : Finset α→Prop) :
    (hostBatchLaw hτ).event (fun T=>P T.val)=(hostBatchLaw hτ').event (fun T=>P T.val) := by
  subst τ'
  rfl

/-- Pointwise forward success in every feasible exposure record. The constants
and original-N threshold precede the frame, time, record and bad source. The
predicate is already expressed on the exact restricted triple for reverse use. -/
theorem bad_source_record_forward_eventually (r b : ℕ) (hr : 3 ≤ r)
    (C B L offset : ℝ) (hC : 0 < C) (hB : 0 ≤ B) (hL : 0 < L) :
    ∃ Km Kc Kg : ℝ, 0 < Km ∧ 0 < Kc ∧ 0 < Kg ∧
    ∀ᶠ N : ℕ in atTop,
      ∀ (M : ℕ) (ell : Fin N → ℕ) (original : Finset (Finset (Fin N))),
      ∀ hadm : CoreAdmissible r M ell original offset,
      letI := hadm.feasible
      ∀ (f : Frame r original) (D : Finset (Fin N)), D.card ≤ b →
      ∀ (j h : ℕ) (c : ℝ), 4*r ≤ h →
      ∀ (hMj : M ≤ j) (hj : j ≤ (completeEdges (Fin N) r).card),
      ∀ (A0 B0 : SimpleHypergraph (Fin N)),
      ∀ hb : 0 < (extensionLaw r M ell).event
        (EdgeComplementEvent r M ell j (samplingUniverse f D) A0 B0),
      ∀ ω : Outcome (Fin N) r M ell,
      EdgeComplementEvent r M ell j (samplingUniverse f D) A0 B0 ω →
      BadSource f j h c C L B ω →
      ∃ hτ : recordBatchSize f j B0 ≤ j-B0.card,
        1-forwardError r C Km Kc Kg N ≤
        (FiniteEntropy.uniform : FiniteEntropy.Law (BatchOrder (j-B0.card))).event
          (fun σ => recordForwardEvent f D A0 B0 ell (M-A0.card) (j-B0.card) (recordBatchSize f j B0)
            (restrictedQBatchObserved r M ell j hMj hj (samplingUniverse f D) A0 B0
              (samplingUniverse_subset_complete f D) hb (recordBatchSize f j B0) hτ (ω,σ))) := by
  obtain ⟨Km,Kc,Kg,hKm,hKc,hKg,hforward⟩ :=
    inherited_forward_witness_eventually r b hr C B L offset hC hB hL
  refine ⟨Km,Kc,Kg,hKm,hKc,hKg,?_⟩
  filter_upwards [hforward] with N hf
  intro M ell original hadm
  letI := hadm.feasible
  intro f D hD j h c hh hMj hj A0 B0 hb ω he hbad
  obtain ⟨hτ,hprob⟩ := hf M ell original hadm f D hD j h c ω hh hMj hj hbad.1 hbad.2.1
    (by simpa only [Frame.candidateBadAtScale,Fintype.card_fin] using hbad.2.2)
  have hτrec : recordBatchSize f j B0 ≤ j-B0.card := by
    rw [record_batchSize f D j hMj hj A0 B0 ω he,
      record_unexposed_card f D j hMj hj A0 B0 ω he] at hτ
    exact hτ
  refine ⟨hτrec,?_⟩
  apply record_forward_lower_transfer f D j hMj hj A0 B0 hb hτrec ω he
    (forwardError r C Km Kc Kg N)
  have ht := record_batchSize f D j hMj hj A0 B0 ω he
  have ht' : recordBatchSize f j B0 ≤ (unexposed f D (extensionState ω.1 ω.2 j)).card := by
    rw [record_unexposed_card f D j hMj hj A0 B0 ω he]
    exact hτrec
  rw [←hostBatch_event_size_eq _ _ _ ht hτ ht' (ForwardWitnessSuccess f D ω.1.val ell (extensionState ω.1 ω.2 j))]
  exact hprob
end LooseHamilton.CandidateBalance
