module

public import HittingTimeLooseHamilton.FrameFinalRecordBound
public import HittingTimeLooseHamilton.FrameFinalRate

public section

noncomputable section
namespace LooseHamilton.CandidateBalance
open Finset AuxiliaryFrame FrameSurvival Filter FrameScales Topology

/-- Every positive-probability exposure record has the final exponential
bound, with rate depending only on r. A record with no bad source contributes
zero; otherwise one actual bad source supplies the record's batch lower bound.
No source condition is moved into the conditioned probability law. -/
theorem record_exponential_bound_eventually (r b : ℕ) (hr : 3≤r)
    (C B L offset : ℝ) (hC : 0<C) (hB : 0≤B) (hL : 0<L) :
    ∀ᶠ N : ℕ in atTop, RecordExponentialBound r b C B L offset N (finalRate r) := by
  classical
  obtain ⟨err,hlim,hbound⟩ := record_candidate_bound_eventually r b hr C B L offset hC hB hL
  filter_upwards [hbound,hlim.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1/2)),
    inherited_sampling_parameters_eventually r b hr C hC.le,
    eventually_final_exponential r (by omega)] with N hb he hsampling hscalar
  intro M ell original hadm
  letI := hadm.feasible
  intro f D hD j h c hh hMj hj A0 B0 hrecord
  let E := EdgeComplementEvent r M ell j (samplingUniverse f D) A0 B0
  let p := ((extensionLaw r M ell).condition E hrecord).event (BadSource f j h c C L B)
  by_cases hex : ∃ω : Outcome (Fin N) r M ell, E ω ∧ BadSource f j h c C L B ω
  · obtain ⟨ω,hE,hbad⟩ := hex
    have hparams := hsampling M ell original offset hadm f D hD j h c L ω hMj hj hbad.1
    have hlower : nu N*L1 N/(16*(r:ℝ))≤(recordBatchSize f j B0:ℝ) := by
      have hlow := hparams.2.2.2.2.2.2.2.2.2.1
      rwa [record_batchSize f D j hMj hj A0 B0 ω hE] at hlow
    have hrec := hb.2.2 M ell original hadm f D hD j h c hh hMj hj A0 B0 hrecord
    exact hscalar p (err N) (recordBatchSize f j B0)
      (((extensionLaw r M ell).condition E hrecord).event_nonneg _) he.le hlower hrec
  · rw [condition_event_eq_joint]
    have hz := (extensionLaw r M ell).event_eq_zero_of_false
      (E := fun ω => E ω ∧ BadSource f j h c C L B ω) (fun ω hω => hex ⟨ω,hω⟩)
    change _ / _ ≤ _
    rw [hz,zero_div]
    exact (Real.exp_pos _).le
end LooseHamilton.CandidateBalance
