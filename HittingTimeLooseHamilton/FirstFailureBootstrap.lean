module

public import HittingTimeLooseHamilton.FirstFailureFinite
public import HittingTimeLooseHamilton.FirstFailureInitial
public import HittingTimeLooseHamilton.FirstFailureRatesCore
public import HittingTimeLooseHamilton.FirstFailureMarginalCap
public import HittingTimeLooseHamilton.FirstFailureEvents

public section

/-! The Section 11 first-failure bootstrap. All constants are chosen before
the offset bound and the probability tolerance. Theorem 1.2's benchmark
conversion is kept separate. -/
noncomputable section
namespace LooseHamilton.FirstFailure
open Filter FirstFailureRates

theorem first_failure_bootstrap (r : ℕ) (hr : 3 ≤ r) : Statement r := by
  obtain ⟨D₀,hD₀,hcap⟩ := UniformMarginalCap.uniform_marginal_cap r hr
  let D : ℝ := D₀+1
  have hD : 1 ≤ D := by dsimp [D]; linarith
  have hDpos : 0 < D := by linarith
  let C : ℝ := budgetCoefficient r D
  have hC : 0 < C := budgetCoefficient_pos hr hDpos
  refine ⟨D,hD,1+C,by positivity,?_⟩
  intro offset hoff ε hε
  obtain ⟨Ncap,hNcap⟩ := hcap offset hoff (ε/2) (by positivity)
  obtain ⟨Nrates,hNrates⟩ := eventually_atTop.mp
    (eventually_core_parameters r hr D hDpos offset hoff (ε/2) (by positivity))
  obtain ⟨Nfull,hNfull⟩ := eventually_atTop.mp (eventually_complete_count_pos r hr)
  refine ⟨max Ncap (max Nrates Nfull),?_⟩
  intro N hN m ell markers hadm
  letI : Nonempty (TerminalState (Fin N) r m ell) := hadm.feasible
  have hN₁ : Ncap ≤ N := (le_max_left _ _).trans hN
  have hN₂ : Nrates ≤ N := (le_max_left _ _).trans ((le_max_right _ _).trans hN)
  have hN₃ : Nfull ≤ N := (le_max_right _ _).trans ((le_max_right _ _).trans hN)
  obtain ⟨hm,hsmall,ha,hW,hVW,hmargin,htail⟩ := hNrates N hN₂ m ell markers hadm
  have hfull := hNfull N hN₃ m ell markers offset hadm
  have hcap' : (extensionLaw r m ell).event (UniformMarginalCap.Failure markers D) ≤ ε/2 := by
    apply le_trans ((extensionLaw r m ell).event_mono
      (marginal_failure_mono markers (show D₀ ≤ D by dsimp [D]; linarith)))
    exact hNcap N hN₁ m ell markers hadm
  have hb : (N:ℝ)/Real.log N + C*((N:ℝ)/Real.log N) ≤
      (1+C)*N/Real.log N := by ring_nf; rfl
  have hbound := finite_probability_bound markers ell D ((N:ℝ)/Real.log N)
    ((1+C)*N/Real.log N) (C*((N:ℝ)/Real.log N)) hr hfull hm hD hsmall
    ha hW hVW hb hmargin
  exact hbound.trans (by linarith)

end LooseHamilton.FirstFailure

namespace LooseHamilton
/-- First-failure exclusion and uniform O_r(N/log N) baseline error. -/
theorem firstFailureBootstrap : FirstFailureBootstrap :=
  FirstFailure.first_failure_bootstrap
end LooseHamilton
