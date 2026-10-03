module

public import HittingTimeLooseHamilton.FirstFailureRatesScalar

public section

noncomputable section
namespace LooseHamilton.FirstFailureRates
open Filter

/-- The variance constant depends only on the fixed uniformity and marginal cap. -/
@[expose] def budgetCoefficient (r : ℕ) (C0 : ℝ) : ℝ := 2*r*C0^2

theorem budgetCoefficient_pos {r : ℕ} (hr : 3 ≤ r) {C0 : ℝ} (hC0 : 0 < C0) :
    0 < budgetCoefficient r C0 := by
  unfold budgetCoefficient
  have : (0:ℝ)<r := by exact_mod_cast (show 0<r by omega)
  positivity

/-- Uniform scalar parameters for the first-failure argument. The variance
budget is inflated to a positive number, so the actual variance may vanish. -/
theorem eventually_core_parameters (r : ℕ) (hr : 3 ≤ r) (C0 : ℝ) (hC0 : 0 < C0)
    (offset : ℝ) (hoff : 0 ≤ offset) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ (m : ℕ) (ell : Fin N → ℕ)
      (markers : Finset (Finset (Fin N))), CoreAdmissible r m ell markers offset →
      let a := (N:ℝ)/Real.log N
      let W := budgetCoefficient r C0*a
      0 < m ∧ C0*ordinaryEdgeCount r markers/m ≤ (1/2:ℝ) ∧
      0 < a ∧ 0 < W ∧
      StoppedCounting.variance C0 (ordinaryEdgeCount r markers) m
        (completeEdges (Fin N) r).card ≤ W ∧
      a+W < (N:ℝ)/Real.sqrt (Real.log N) ∧
      (terminalFeasibilityProbability r m ell)⁻¹ * Real.exp (-a^2/(2*W)) ≤ ε := by
  obtain ⟨N₀,hN₀⟩ := terminal_feasibility_core r hr offset hoff
  filter_upwards [eventually_core_budget r hr C0 hC0.le,
    eventually_scalar_rates (budgetCoefficient r C0) (budgetCoefficient_pos hr hC0) ε hε,
    eventually_ge_atTop N₀] with N hb hs hN
  intro m ell markers hadm
  obtain ⟨hm,hcap,hv⟩ := hb m ell markers offset hadm
  have hβ := hN₀ (Fin N) (by simpa using hN) m ell markers hadm
  simp only [Fintype.card_fin] at hβ
  dsimp only
  refine ⟨hm,hcap,hs.2.2.1,hs.2.2.2.1,hv,?_,hs.2.2.2.2.2 _ hβ⟩
  convert hs.2.2.2.2.1 using 1; ring
end LooseHamilton.FirstFailureRates
