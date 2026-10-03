module

public import HittingTimeLooseHamilton.RootSamplingFinite

public section

/-! Adaptive root-free tests are averaged over their observations. There is
no union bound over terminal/current root-free configurations. -/
noncomputable section
namespace LooseHamilton
open Finset

/-- Forget a finite observation for a test depending on that observation.
The observable gate is part of the bad event, not a conditioning hypothesis. -/
theorem adaptive_observation_bad_event_le
    {Ω I : Type*} [Fintype Ω] [Fintype I]
    (p : FiniteEntropy.Law Ω) (E : Ω → Prop) (obs : Ω → I)
    (gate : I → Prop) (test : I → Ω → Prop) (γ : ℝ) (hγ : 0 ≤ γ)
    (hbound : ∀ i, gate i → ∀ hi : 0 < p.event (fun ω => E ω ∧ obs ω=i),
      (p.condition (fun ω => E ω ∧ obs ω=i) hi).event (test i) ≤ γ) :
    p.event (fun ω => E ω ∧ gate (obs ω) ∧ test (obs ω) ω) ≤ γ := by
  classical
  have hb := joint_event_le_sum_conditional_bounds p E
    (fun ω => gate (obs ω) ∧ test (obs ω) ω) obs (fun _ => γ) (by
      intro i hi
      have he := conditional_event_congr_on p (fun ω => E ω ∧ obs ω=i)
        (fun ω => gate (obs ω) ∧ test (obs ω) ω)
        (fun ω => gate i ∧ test i ω) hi (by intro ω hω; rw [hω.2])
      rw [he]
      by_cases hg : gate i
      · simpa only [hg, true_and] using hbound i hg hi
      · simpa [hg, FiniteEntropy.Law.event] using hγ)
  rw [←mul_sum, ←event_eq_sum_observation_fibres p E obs] at hb
  exact hb.trans (mul_le_of_le_one_right hγ (p.event_le_one E))

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Data revealed while withholding all root edges, in both the terminal and
current graph. A root-link test may be any function of this data. -/
@[expose] def rootFreePairObservation (r M : ℕ) (ell : V → ℕ) (m : ℕ) (y : V)
    (ω : TerminalState V r M ell × MissingOrder V r M) :
    SimpleHypergraph V × SimpleHypergraph V :=
  (rootFreeEdges y ω.1.val,rootFreeEdges y (extensionState ω.1 ω.2 m))

/-- Unconditional adaptive-test estimate. The deficit, degree and density
restrictions are intersected with the failure event, never conditioned on. -/
theorem root_free_adaptive_test_probability
    (r M : ℕ) (ell : V → ℕ) [Nonempty (TerminalState V r M ell)]
    (m : ℕ) (hMm : M ≤ m) (hm : m ≤ (completeEdges V r).card)
    (y : V) (R : SimpleHypergraph V)
    (Γ : SimpleHypergraph V × SimpleHypergraph V → SimpleHypergraph V)
    (h qmin : ℕ) (ρ : ℝ)
    (hR : R ⊆ rootEdgeUniverse r y) (hRh : R.card ≤ h)
    (hU : 0 < (rootEdgeUniverse r y).card) (hh : 2*h ≤ (rootEdgeUniverse r y).card)
    (hqmin : 12*(h+1) ≤ qmin) (hρ0 : 0 ≤ ρ) (hρ : ρ ≤ 1/8)
    (hΓ : ∀ data, Γ data ⊆ rootEdgeUniverse r y) :
    (extensionLaw r M ell).event (fun ω =>
      R ⊆ (rootSamplingPair r M ell m ω).2 ∧
      (∑ v, rootAdjustedDeficit y ell (rootFreePairObservation r M ell m y ω).1 v) ≤ 1 ∧
      qmin ≤ m-(rootFreePairObservation r M ell m y ω).2.card ∧
      rootLinkDensity r y (Γ (rootFreePairObservation r M ell m y ω)) ≤ ρ ∧
      RootLinkBad (Γ (rootFreePairObservation r M ell m y ω))
        (m-(rootFreePairObservation r M ell m y ω).2.card) (rootSamplingPair r M ell m ω)) ≤
      (8*ρ)^((qmin:ℝ)/4) := by
  classical
  let obs := rootFreePairObservation r M ell m y
  let gate := fun data : SimpleHypergraph V × SimpleHypergraph V =>
    (∑ v, rootAdjustedDeficit y ell data.1 v) ≤ 1 ∧
    qmin ≤ m-data.2.card ∧ rootLinkDensity r y (Γ data) ≤ ρ
  let test := fun data ω => RootLinkBad (Γ data) (m-data.2.card) (rootSamplingPair r M ell m ω)
  have havg := adaptive_observation_bad_event_le (extensionLaw r M ell)
    (fun ω => R ⊆ (rootSamplingPair r M ell m ω).2) obs gate test
    ((8*ρ)^((qmin:ℝ)/4)) (Real.rpow_nonneg (by positivity) _) (by
      intro data hg hi
      rcases data with ⟨F₀,H₀⟩
      have he : (fun ω => R ⊆ (rootSamplingPair r M ell m ω).2 ∧ obs ω=(F₀,H₀)) =
          (fun ω => RootFreeObservation y F₀ H₀ R (rootSamplingPair r M ell m ω)) := by
        funext ω
        simp only [obs, rootFreePairObservation, RootFreeObservation, rootSamplingPair,
          Prod.mk.injEq, and_comm, and_left_comm, and_assoc, Prod.mk.eta]
      simp only [he] at hi ⊢
      have hb := root_link_sampling_finite r M ell m hMm hm y F₀ H₀ R (Γ (F₀,H₀)) h
        (hΓ (F₀,H₀)) hR hRh hU hh (hqmin.trans hg.2.1) hg.1 (hg.2.2.trans hρ) hi
      apply hb.trans
      calc
        _ ≤ (8*ρ)^(((m-H₀.card:ℕ):ℝ)/4) := Real.rpow_le_rpow
          (by unfold rootLinkDensity; positivity) (by linarith [hg.2.2]) (by positivity)
        _ ≤ _ := Real.rpow_le_rpow_of_exponent_ge' (by positivity) (by linarith)
          (by positivity) (by exact_mod_cast (div_le_div_of_nonneg_right
            (Nat.cast_le.mpr hg.2.1 : (qmin:ℝ) ≤ (m-H₀.card:ℕ)) (by norm_num : (0:ℝ) ≤ 4))))
  simpa only [gate, test, obs, and_assoc] using havg
end LooseHamilton
