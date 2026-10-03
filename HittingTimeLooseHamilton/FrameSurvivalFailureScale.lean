module

public import HittingTimeLooseHamilton.CandidateBalanceProbabilityRates

public section

noncomputable section
namespace LooseHamilton.FrameScales
open Filter Topology

/-- The common bound used for each individual survival failure. -/
@[expose] def survivalFailureBound (K : ℝ) (N : ℕ) : ℝ :=
  K*(L2 N)^(-24/25:ℝ)/(alpha N/100000)^2

lemma survivalFailureBound_nonneg {K : ℝ} (hK : 0≤K) (N : ℕ) (hN : 0≤L2 N) :
    0≤survivalFailureBound K N := by unfold survivalFailureBound; positivity

/-- The proved failure scale remains negligible after any fixed power of
alpha is lost to an averaging/Markov step. This does not assert simultaneous
concentration of the completion families. -/
theorem survivalFailureBound_div_alpha_tendsto {K : ℝ} (hK : 0≤K) (a : ℝ) :
    Tendsto (fun N => survivalFailureBound K N/(alpha N)^a) atTop (nhds 0) := by
  apply failure_probability_div_alpha_power (p := survivalFailureBound K) (C := K)
    (by filter_upwards [eventual_range] with N hN; exact survivalFailureBound_nonneg hK N hN.2.1.le) ?_ a
  filter_upwards [eventual_range] with N hN
  unfold survivalFailureBound
  have ha := hN.2.2.2.1
  have hh : (alpha N/100000)^(-2:ℝ) = ((alpha N/100000)^2)⁻¹ := by
    rw [Real.rpow_neg (by positivity : 0≤alpha N/100000), Real.rpow_two]
  rw [hh]
  apply le_of_eq
  ring

theorem survivalFailureBound_tendsto_zero {K : ℝ} (hK : 0≤K) :
    Tendsto (survivalFailureBound K) atTop (nhds 0) := by
  simpa using survivalFailureBound_div_alpha_tendsto hK 0
end LooseHamilton.FrameScales
