module

public import HittingTimeLooseHamilton.CoreParameters
public import HittingTimeLooseHamilton.CoreSeparatedBlocks
public import HittingTimeLooseHamilton.TightStoppingWindow
public import HittingTimeLooseHamilton.ExceptionalSet

public section

/-! The exact core parameter event has probability tending to one under the
original edge-order process, for each fixed r. -/
noncomputable section
namespace LooseHamilton
open Filter Finset
open scoped Topology BigOperators

/-- All permitted block choices satisfy the paper's core parameters. Divisibility
is inherited from the original vertex count, as in the standing hypothesis. -/
@[expose] def exactCoreParameterEvent {n r : ℕ} (σ : EdgeOrder (Fin n) r) : Prop :=
  ∃ t : ℕ, tauOne σ = (t : WithTop ℕ) ∧
    Nonempty (CoreBlockFamily r (processState σ t) (lowDegreeVertices (processState σ t))) ∧
    ∀ C : CoreBlockFamily r (processState σ t) (lowDegreeVertices (processState σ t)),
      r-1 ∣ n →
      CoreAdmissible (V := ↥C.coreVertices) r (t-(traceOn C.deleted (processState σ t)).card)
        (fun w => coreLowerBound C.deleted (traceOn C.deleted (processState σ t)) w.val)
        (restrictEdges C.coreVertices C.markers) ((2*(r-2) : ℕ)+2)

theorem exactCoreParameterEvent_of_good_eventually {r : ℕ} (hr : 3 ≤ r) :
    ∀ᶠ n : ℕ in atTop, ∀ σ : EdgeOrder (Fin n) r,
      stoppedExceptionalEvent 20 σ → ¬ coreStoppingWindowFailure σ → exactCoreParameterEvent σ := by
  filter_upwards [core_admissible_eventually hr,coreWindow_density_bound_eventually (by omega : 1 ≤ r)]
    with n hparams hdensity
  intro σ hg hw
  obtain ⟨t,ht,hgood⟩ := hg
  obtain ⟨t',ht',hlo,hhi⟩ := not_not.mp hw
  have heq : t=t' := WithTop.coe_eq_coe.mp (ht.symm.trans ht')
  subst t'
  obtain ⟨htbound,hNI⟩ := firstTime_spec (completeEdges (Fin n) r).card (processState σ) NoIsolated (t := t) ht
  have hcard : (processState σ t).card = t := by rw [processState_card,min_eq_left htbound]
  refine ⟨t,ht,⟨CoreBlockFamily.ofSeparated hr (processState_subset σ t)
    (fun v _ => hNI v) hgood.separated⟩,?_⟩
  intro C hdiv
  have h := hparams (processState σ t) (processState_subset σ t) hNI hgood C
    (by rw [hcard]; exact hdensity t hlo hhi) hdiv
  simpa only [hcard] using h

/-- Finite union bound for a target which contains a good event minus a bad event. -/
theorem event_compl_le_two_errors {Ω : Type*} [Fintype Ω]
    (p : FiniteEntropy.Law Ω) (G B E : Ω → Prop)
    (h : ∀ ω, G ω → ¬ B ω → E ω) :
    1-p.event E ≤ (1-p.event G)+p.event B := by
  classical
  let A : Bool → Ω → Prop := fun b ω => if b then B ω else ¬ G ω
  rw [← FiniteEntropy.Law.event_compl]
  calc
    _ ≤ p.event (fun ω => ∃ b, A b ω) := p.event_mono (by
      intro ω he
      by_cases hg : G ω
      · exact ⟨true,by simpa only [A,ite_true] using (by
          by_contra hb
          exact he (h ω hg hb) : B ω)⟩
      · exact ⟨false,hg⟩)
    _ ≤ ∑ b : Bool, p.event (A b) := p.finite_union_bound A
    _ = _ := by simp [A,FiniteEntropy.Law.event_compl,add_comm]

/-- Proposition 3.3's full parameter assertion, with no unproved probability
input: both Lemma 3.2 and the sharper stopping window are discharged. -/
theorem exact_core_parameters_whp {r : ℕ} (hr : 3 ≤ r) :
    Tendsto (fun n => (processLaw (Fin n) r).event exactCoreParameterEvent) atTop (𝓝 1) := by
  have hsum := ((tendsto_const_nhds (x := (1 : ℝ))).sub
    (small_separated_exceptional_set hr)).add (core_stopping_window_tendsto_zero hr)
  simp only [sub_self,zero_add] at hsum
  have hzero : Tendsto (fun n => 1-(processLaw (Fin n) r).event exactCoreParameterEvent)
      atTop (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall fun n =>
      sub_nonneg.mpr ((processLaw (Fin n) r).event_le_one _)) ?_ hsum
    filter_upwards [exactCoreParameterEvent_of_good_eventually hr] with n hn
    exact event_compl_le_two_errors (processLaw (Fin n) r) (stoppedExceptionalEvent 20)
      coreStoppingWindowFailure exactCoreParameterEvent hn
  have h := (tendsto_const_nhds (x := (1 : ℝ))).sub hzero
  simpa only [sub_zero,sub_sub_cancel] using h
end LooseHamilton
