module

public import HittingTimeLooseHamilton.TerminalRegularityProbability
public import HittingTimeLooseHamilton.TerminalRegularityDeficit

public section

/-! Proposition 4.3 of the supplied general-r loose-Hamilton manuscript. -/
noncomputable section
namespace LooseHamilton
open Filter

/-- The deficit clause holds on the regularity event for every fixed deletion budget. -/
theorem terminal_deficit_bound (r : ℕ) (C B : ℝ) (h : ℕ) : TerminalDeficitBound r C B h := by
  obtain ⟨N₀,hN₀⟩ := eventually_atTop.mp (eventually_terminal_regular_deficit B C h)
  refine ⟨N₀,?_⟩
  intro V _ _ hn M ell markers hadm F hF Z hZ
  exact hN₀ (Fintype.card V) hn V rfl r M ell markers hadm F hF Z hZ

/-- Proposition 4.3: terminal regularity with probability tending to one,
and the total positive deficit bound after every fixed bounded vertex deletion. -/
theorem proposition43 : Proposition43 := by
  intro r hr
  refine ⟨terminalRegularityConstant,terminalRegularityConstant_pos,?_⟩
  intro B hB
  exact ⟨terminal_regularity_whp r hr B hB,
    fun h => terminal_deficit_bound r terminalRegularityConstant B h⟩
end LooseHamilton
