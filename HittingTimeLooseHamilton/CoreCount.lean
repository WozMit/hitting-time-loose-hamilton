module

public import HittingTimeLooseHamilton.CoreCountFinite
public import HittingTimeLooseHamilton.CoreCountBenchmark
public import HittingTimeLooseHamilton.FirstFailureBootstrap

public section

/-! Theorem 1.2: Conditioned core count, with uniform instance quantifiers. -/
noncomputable section
namespace LooseHamilton.CoreCount
open Filter

theorem conditioned_core_count (r : ℕ) (hr : 3 ≤ r) : Statement r := by
  obtain ⟨D,_hD,B,hB,hpath⟩ := FirstFailure.first_failure_bootstrap r hr
  obtain ⟨Nbench,hNbench⟩ := eventually_atTop.mp
    (CoreCountBenchmark.eventually_core_benchmark r hr)
  refine ⟨B+1,by linarith,?_⟩
  intro offset hoff ε hε
  obtain ⟨Npath,hNpath⟩ := hpath offset hoff ε hε
  refine ⟨max Nbench Npath,?_⟩
  intro N hN m ell markers hadm
  letI : Nonempty (TerminalState (Fin N) r m ell) := hadm.feasible
  exact terminal_probability_bound markers ell D B ε
    (hNbench N ((le_max_left _ _).trans hN) m ell markers offset hadm)
    (hNpath N ((le_max_right _ _).trans hN) m ell markers hadm)

end LooseHamilton.CoreCount

namespace LooseHamilton
/-- Conditioned core count under the uniform feasible terminal law. -/
theorem theorem12 : Theorem12 := CoreCount.conditioned_core_count
end LooseHamilton
