module

public import HittingTimeLooseHamilton.BiasedEntropyBudget
public import HittingTimeLooseHamilton.BiasedRoleAssembly

public section

/-! Theorem 6.1: all intermediate entropy, clone, and probability bounds are proved. -/
noncomputable section
namespace LooseHamilton

/-- Biased-role entropy stability for arbitrary distributions on actual
connected spanning mixed cycles, with exactly the printed error budget. -/
theorem theorem61 : Theorem61 :=
  theorem61_of_entropy_deficit_bound (by
    intro r hr C hC
    exact BiasedRoleInstance.eventual_entropy_deficit_bound r hr C hC)

end LooseHamilton
