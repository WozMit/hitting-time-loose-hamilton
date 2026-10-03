module

public import HittingTimeLooseHamilton.HittingTimeStatement
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Tactic

public section

noncomputable section
namespace LooseHamilton.HittingTimeConclusion
open Filter

/-- The epsilon--N conclusion gives the literal probability-one limit along
all multiples of r-1, without imposing any hypothesis on the sampled graph. -/
theorem limit_of_statement {r : ℕ} (hr : 3 ≤ r) (h : Statement r) :
    Tendsto (fun q : ℕ => hittingTimeProbability (Fin ((r-1)*q)) r) atTop (nhds 1) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨N₀,hN₀⟩ := h (ε/2) (by positivity)
  refine ⟨N₀,?_⟩
  intro q hq
  have hn : N₀ ≤ (r-1)*q := by
    have hr1 : 1 ≤ r-1 := by omega
    nlinarith
  have hlo := hN₀ ((r-1)*q) hn (dvd_mul_right _ _)
  have hhi := hittingTimeProbability_le_one (V:=Fin ((r-1)*q)) r
  rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hhi)]
  linarith

end LooseHamilton.HittingTimeConclusion
