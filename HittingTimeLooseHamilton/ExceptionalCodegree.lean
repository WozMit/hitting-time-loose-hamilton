module

public import HittingTimeLooseHamilton.PairDegreeAsymptotic
public import HittingTimeLooseHamilton.ExceptionalWindowScales
public import HittingTimeLooseHamilton.ExceptionalSetReduction

public section

/-! The codegree failure in the exceptional-set reduction has vanishing probability. -/
noncomputable section
namespace LooseHamilton
open Filter
open scoped Topology

theorem exceptional_pair_failure_tendsto_zero {r : ℕ} (hr : 3 ≤ r) (C : ℝ) :
    Tendsto (fun n : ℕ => (processLaw (Fin n) r).event
      (exceptionalFailure C (exceptionalWindowLo r n) (exceptionalWindowHi r n) 3))
      atTop (𝓝 0) := by
  have h := process_pair_degree_three_tendsto_zero (by omega : 2 ≤ r)
    (exceptionalWindowHi_ratio_tendsto r)
  convert h using 1
  funext n
  congr 1
  funext σ
  apply propext
  simp only [exceptionalFailure, not_forall, Classical.not_imp, not_le, Nat.add_one_le_iff, exists_prop]
end LooseHamilton
