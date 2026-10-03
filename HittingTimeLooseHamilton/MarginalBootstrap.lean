module

public import HittingTimeLooseHamilton.BootstrapAllEdgeMaximum
public import HittingTimeLooseHamilton.BootstrapMarginalConversion

public section

/-! # Completed deterministic marginal bootstrap (item 33)
The supplied manuscript's conclusion in the proof of `thm:marginal`, with the
registration and private-mobility amendments. The probability of the resulting
marginal event is deliberately left to item 34. -/
noncomputable section
namespace LooseHamilton.MarginalBootstrap
open Finset Filter BootstrapCatalogue BootstrapConstants

/-- Constants and the fixed registry precede the outcome; one common event
controls every eligible time and every true-edge marginal, including zero counts. -/
@[expose] def DeterministicStatement (r : ℕ) (hr : 3 ≤ r) (c C D : ℝ) : Prop :=
    ∀ᶠ N : ℕ in atTop, ∀ (m : ℕ) (ell : Fin N → ℕ)
      (M : Finset (Finset (Fin N))) (offset : ℝ)
      (hadm : CoreAdmissible r m ell M offset),
      ∃ hroom : 2*M.card+2 ≤ Fintype.card (Fin N),
      ∀ (h hR : ℕ) (L : ℝ)
        (ω : CandidateBalance.Outcome (Fin N) r m ell),
      RootFreeCommonEvent
        (fixedRegistry (h:=hR) hadm.marker_matching hr hroom
          (rootThreshold r) (rootThreshold r) (portThreshold r c))
        h c C L 2 (rootConstant c) ω →
      ∀ j : ℕ, m ≤ j → j ≤ (completeEdges (Fin N) r).card →
      let H := extensionState ω.1 ω.2 j
      let X := cycleCount r M H (originalPorts M)
      logarithmicBaseline r (ordinaryEdgeCount r M) j M -
        (N:ℝ)/Real.sqrt (Real.log N) ≤ Real.log (X:ℝ) →
      ∀ e : Finset (Fin N),
      cycleMarginal r M H (originalPorts M) e ≤ D/meanDegree (V:=Fin N) r j ∧
      cycleMarginal r M H (originalPorts M) e ≤ (2*D)*(ordinaryEdgeCount r M:ℝ)/j

/-- The full conditional deterministic theorem, with explicit cap coefficient.
No entropy budget, density, mobility, source-size or positive-cycle premise is added. -/
theorem deterministic_marginal_bootstrap (r : ℕ) (hr : 3 ≤ r) (c C : ℝ)
    (hc : 0<c) (hC : 0≤C) :
    DeterministicStatement r hr c C (BootstrapAllEdgeMaximum.constant r c) := by
  filter_upwards [BootstrapAllEdgeMaximum.eventually_all_edge_marginals r hr c C hc hC]
    with N hcap
  intro m ell M offset hadm
  obtain ⟨hroom,hcap⟩ := hcap m ell M offset hadm
  refine ⟨hroom,?_⟩
  intro h hR L ω hω j hj hK H X hAX e
  have he := hcap h hR L ω hω j hj hK hAX e
  exact ⟨he,BootstrapMarginalConversion.of_admissible hadm j
    (BootstrapAllEdgeMaximum.constant_nonneg r c) he⟩

/-- Positivity of the chosen coefficient, uniformly over the regularity scale. -/
theorem cap_constant_pos {r : ℕ} (hr : 3 ≤ r) (c : ℝ) :
    0 < BootstrapAllEdgeMaximum.constant r c := by
  unfold BootstrapAllEdgeMaximum.constant
  apply mul_pos (Nat.cast_pos.mpr (Nat.choose_pos (by omega : 2≤r)))
  exact (BootstrapPortCap.constant_pos hr c).trans_le (le_max_right _ _)

/-- Compatibility of fixed regularity constants with the already proved common
-event probability theorem. This concerns the common event, not the marginal event. -/
@[expose] def CommonEventConstants (r : ℕ) (c C : ℝ) : Prop :=
    ∀ B offset L cRoot : ℝ, 0≤B → 0≤offset → 0<L → 0<cRoot →
      ∀ ε : ℝ, 0<ε → ∃ N₀ : ℕ,
      ∀ N : ℕ, N₀≤N → ∀ m : ℕ, ∀ ell : Fin N → ℕ,
      ∀ M : Finset (Finset (Fin N)),
      ∀ admissible : CoreAdmissible r m ell M offset,
      ∀ tests : RootFreeTestIndexing.RootTestIndex r M → RegisteredRootTest (Fin N) r (4*r),
      letI : Nonempty (TerminalState (Fin N) r m ell) := admissible.feasible
      1-ε ≤ (extensionLaw r m ell).event
        (RootFreeCommonEvent tests (4*r) c C L B cRoot)

/-- For each fixed r the constants can be fixed once, independently of N,
matching, instance and outcome, while retaining the common-event probability
compatibility needed by the subsequent probabilistic theorem. -/
theorem fixed_constants_bootstrap (r : ℕ) (hr : 3 ≤ r) :
    ∃ c C D : ℝ, 0<c ∧ 0<C ∧ 0<D ∧
      CommonEventConstants r c C ∧ DeterministicStatement r hr c C D := by
  obtain ⟨c,C,hc,hC,hprob⟩ := root_free_common_event_whp r hr (4*r) (4*r) le_rfl
  exact ⟨c,C,BootstrapAllEdgeMaximum.constant r c,hc,hC,cap_constant_pos hr c,hprob,
    deterministic_marginal_bootstrap r hr c C hc hC.le⟩

end LooseHamilton.MarginalBootstrap
