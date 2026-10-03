module

public import HittingTimeLooseHamilton.CoreHighProbability

public section

/-! The two previously proved stopping-time events, before any exposure
conditioning. They are used to certify favourable observation fibres. -/
noncomputable section
namespace LooseHamilton.HittingTimeConclusion
open Filter

@[expose] def Good {n r : ℕ} (σ : EdgeOrder (Fin n) r) : Prop :=
  stoppedExceptionalEvent 20 σ ∧ exactCoreParameterEvent σ

theorem good_event_probability_tendsto_one (r : ℕ) (hr : 3 ≤ r) :
    Tendsto (fun n => (processLaw (Fin n) r).event Good) atTop (nhds 1) := by
  have hzero := ((tendsto_const_nhds (x := (1:ℝ))).sub
    (small_separated_exceptional_set hr)).add
      ((tendsto_const_nhds (x := (1:ℝ))).sub (exact_core_parameters_whp hr))
  simp only [sub_self, zero_add] at hzero
  have hbound : ∀ n : ℕ, 1-(processLaw (Fin n) r).event Good ≤
      (1-(processLaw (Fin n) r).event (stoppedExceptionalEvent 20)) +
      (1-(processLaw (Fin n) r).event exactCoreParameterEvent) := by
    intro n
    have h := event_compl_le_two_errors (processLaw (Fin n) r)
      (stoppedExceptionalEvent 20) (fun σ => ¬ exactCoreParameterEvent σ) Good
      (fun σ hs hn => ⟨hs,not_not.mp hn⟩)
    simpa only [FiniteEntropy.Law.event_compl] using h
  have hz : Tendsto (fun n => 1-(processLaw (Fin n) r).event Good) atTop (nhds 0) :=
    squeeze_zero (fun n => sub_nonneg.mpr ((processLaw (Fin n) r).event_le_one _))
      hbound hzero
  have hh := (tendsto_const_nhds (x := (1:ℝ))).sub hz
  simpa only [sub_zero,sub_sub_cancel] using hh

end LooseHamilton.HittingTimeConclusion
