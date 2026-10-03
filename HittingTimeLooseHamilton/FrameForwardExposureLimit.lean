module

public import HittingTimeLooseHamilton.FrameForwardExposureUniform
public import HittingTimeLooseHamilton.FrameForwardWitnessLimit

public section

noncomputable section
namespace LooseHamilton.CandidateBalance
open Finset AuxiliaryFrame FrameSurvival Filter FrameScales Topology

/-- The same pointwise claim on every feasible complement record, expressed
on the genuine restricted triple rather than a surrogate batch space. -/
@[expose] def RecordPointwiseForwardBound (r b : ℕ) (C B L offset : ℝ) (N : ℕ) (err : ℝ) : Prop :=
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
        1-err ≤
        (FiniteEntropy.uniform : FiniteEntropy.Law (BatchOrder (j-B0.card))).event
          (fun σ => recordForwardEvent f D A0 B0 ell (M-A0.card) (j-B0.card) (recordBatchSize f j B0)
            (restrictedQBatchObserved r M ell j hMj hj (samplingUniverse f D) A0 B0
              (samplingUniverse_subset_complete f D) hb (recordBatchSize f j B0) hτ (ω,σ)))

lemma pointwise_forward_to_record (r b : ℕ) (C B L offset : ℝ) (N : ℕ) (err : ℝ)
    (hf : PointwiseForwardBound r b C B L offset N err) :
    RecordPointwiseForwardBound r b C B L offset N err := by
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
    err
  have ht := record_batchSize f D j hMj hj A0 B0 ω he
  have ht' : recordBatchSize f j B0 ≤ (unexposed f D (extensionState ω.1 ω.2 j)).card := by
    rw [record_unexposed_card f D j hMj hj A0 B0 ω he]
    exact hτrec
  rw [←hostBatch_event_size_eq _ _ _ ht hτ ht' (ForwardWitnessSuccess f D ω.1.val ell (extensionState ω.1 ω.2 j))]
  exact hprob

/-- A single vanishing error works for the original HostBatch experiment and
for every positive-probability complement record, pointwise on each bad source. -/
theorem pointwise_forward_witness_with_records (r b : ℕ) (hr : 3 ≤ r)
    (C B L offset : ℝ) (hC : 0 < C) (hB : 0 ≤ B) (hL : 0 < L) :
    ∃ err : ℕ → ℝ, Tendsto err atTop (nhds 0) ∧
      ∀ᶠ N : ℕ in atTop, 0 ≤ err N ∧ err N < 1 ∧
        PointwiseForwardBound r b C B L offset N (err N) ∧
        RecordPointwiseForwardBound r b C B L offset N (err N) := by
  obtain ⟨err,hlim,hforward⟩ := pointwise_forward_witness r b hr C B L offset hC hB hL
  refine ⟨err,hlim,?_⟩
  filter_upwards [hforward] with N hN
  exact ⟨hN.1,hN.2.1,hN.2.2,pointwise_forward_to_record r b C B L offset N (err N) hN.2.2⟩
end LooseHamilton.CandidateBalance
