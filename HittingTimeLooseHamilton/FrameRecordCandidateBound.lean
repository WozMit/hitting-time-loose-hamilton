module

public import HittingTimeLooseHamilton.FrameForwardExposureLimit
public import HittingTimeLooseHamilton.FrameRecordForwardComparison
public import HittingTimeLooseHamilton.FrameRecordReverseProbability

public section

/-! The recordwise candidate estimate uses precisely Q conditioned on the
edge-complement record. Regularity and entropy remain part of the event. -/
noncomputable section
namespace LooseHamilton.CandidateBalance
open Finset AuxiliaryFrame FrameSurvival Filter FrameScales Topology

/-- Multiplicative candidate bound, uniformly over every feasible fixed record. -/
@[expose] def RecordCandidateBound (r b : ℕ) (C B L offset : ℝ) (N : ℕ) (err : ℝ) : Prop :=
  ∀ (M : ℕ) (ell : Fin N → ℕ) (original : Finset (Finset (Fin N))),
  ∀ hadm : CoreAdmissible r M ell original offset,
  letI := hadm.feasible
  ∀ (f : Frame r original) (D : Finset (Fin N)), D.card ≤ b →
  ∀ (j h : ℕ) (c : ℝ), 4*r ≤ h →
  ∀ (hMj : M ≤ j) (hj : j ≤ (completeEdges (Fin N) r).card),
  ∀ (A0 B0 : SimpleHypergraph (Fin N)),
  ∀ hb : 0 < (extensionLaw r M ell).event
    (EdgeComplementEvent r M ell j (samplingUniverse f D) A0 B0),
    (1-err) * ((extensionLaw r M ell).condition
      (EdgeComplementEvent r M ell j (samplingUniverse f D) A0 B0) hb).event
      (BadSource f j h c C L B) ≤
    Real.exp (-alpha N * recordBatchSize f j B0 / 64)

/-- A record with no bad source contributes zero. Otherwise a bad source
provides batch feasibility, after which forward and reverse estimates compare
on the same product probability space. -/
theorem record_candidate_bound_of_forward (r b : ℕ) (C B L offset : ℝ)
    (N : ℕ) (err : ℝ) (hα : 0 ≤ alpha N) (hsmall : alpha N ≤ 1/16)
    (hf : RecordPointwiseForwardBound r b C B L offset N err) :
    RecordCandidateBound r b C B L offset N err := by
  classical
  intro M ell original hadm
  letI := hadm.feasible
  intro f D hD j h c hh hMj hj A0 B0 hb
  by_cases hex : ∃ ω : Outcome (Fin N) r M ell,
      EdgeComplementEvent r M ell j (samplingUniverse f D) A0 B0 ω ∧
      BadSource f j h c C L B ω
  · obtain ⟨ω,he,hbad⟩ := hex
    obtain ⟨hτ,_⟩ := hf M ell original hadm f D hD j h c hh hMj hj A0 B0 hb ω he hbad
    let W := fun z => recordForwardEvent f D A0 B0 ell
      (M-A0.card) (j-B0.card) (recordBatchSize f j B0)
      (restrictedQBatchObserved r M ell j hMj hj (samplingUniverse f D) A0 B0
        (samplingUniverse_subset_complete f D) hb (recordBatchSize f j B0) hτ z)
    have hlo := conditioned_product_forward_lower (extensionLaw r M ell)
      (EdgeComplementEvent r M ell j (samplingUniverse f D) A0 B0) hb
      (FiniteEntropy.uniform : FiniteEntropy.Law (BatchOrder (j-B0.card)))
      (BadSource f j h c C L B) W err (by
        intro ω' he' hbad'
        obtain ⟨hτ',hp⟩ := hf M ell original hadm f D hD j h c hh hMj hj A0 B0 hb ω' he' hbad'
        exact hp)
    exact hlo.trans (record_reverse_q_event_bound M ell f D j hMj hj A0 B0 hb
      (recordBatchSize f j B0) hτ hα hsmall)
  · rw [condition_event_eq_joint]
    have hz := (extensionLaw r M ell).event_eq_zero_of_false
      (E := fun ω => EdgeComplementEvent r M ell j (samplingUniverse f D) A0 B0 ω ∧
        BadSource f j h c C L B ω) (fun ω hω => hex ⟨ω,hω⟩)
    rw [hz,zero_div,mul_zero]
    exact (Real.exp_pos _).le

/-- One vanishing error and one threshold work before choosing the frame,
time or feasible complement record. No stronger conditioned law is used. -/
theorem record_candidate_bound_eventually (r b : ℕ) (hr : 3 ≤ r)
    (C B L offset : ℝ) (hC : 0 < C) (hB : 0 ≤ B) (hL : 0 < L) :
    ∃ err : ℕ → ℝ, Tendsto err atTop (nhds 0) ∧
      ∀ᶠ N : ℕ in atTop, 0 ≤ err N ∧ err N < 1 ∧
        RecordCandidateBound r b C B L offset N (err N) := by
  obtain ⟨err,hlim,hf⟩ := pointwise_forward_witness_with_records r b hr C B L offset hC hB hL
  refine ⟨err,hlim,?_⟩
  have hsmall : ∀ᶠ N : ℕ in atTop, alpha N < 1/16 :=
    alpha_tendsto_zero.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1/16))
  filter_upwards [hf,FrameScales.eventual_range,hsmall] with N hN hs ha
  exact ⟨hN.1,hN.2.1,record_candidate_bound_of_forward r b C B L offset N (err N)
    hs.2.2.2.1.le ha.le hN.2.2.2⟩
end LooseHamilton.CandidateBalance
