module

public import HittingTimeLooseHamilton.ExceptionalStoppingWindow
public import HittingTimeLooseHamilton.ExceptionalLowSetAsymptotic
public import HittingTimeLooseHamilton.MaximumDegreeAsymptotic
public import HittingTimeLooseHamilton.ExceptionalCodegree
public import HittingTimeLooseHamilton.ExceptionalPathAsymptotic

public section

/-! Lemma 3.2: the small and separated exceptional set at the original
minimum-degree-one stopping time. All probability estimates are proved for
the original uniform edge-order process, and all error terms are discharged. -/
noncomputable section
namespace LooseHamilton
open Filter Finset
open scoped Topology

/-- The complete exceptional-set event holds with probability tending to one.
The proof gives the absolute maximum-degree constant 20, which is stronger
than permitting the manuscript's constant to depend on the fixed uniformity. -/
theorem small_separated_exceptional_set {r : ℕ} (hr : 3 ≤ r) :
    Tendsto (fun n : ℕ => (processLaw (Fin n) r).event (stoppedExceptionalEvent 20))
      atTop (𝓝 1) := by
  apply exceptional_probability_tendsto_of_failures 20
    (exceptionalWindowLo r) (exceptionalWindowHi r) lowerDegreeBase_eventually_pos
  have h : ∀ i : Fin 5, Tendsto (fun n : ℕ => (processLaw (Fin n) r).event
      (exceptionalFailure 20 (exceptionalWindowLo r n) (exceptionalWindowHi r n) i))
      atTop (𝓝 0) := by
    intro i
    fin_cases i
    · exact exceptional_stopping_failure_tendsto_zero hr 20
    · exact exceptional_failure_one_tendsto_zero hr 20
    · exact exceptionalFailure_maximum_degree_tendsto hr
    · exact exceptional_pair_failure_tendsto_zero hr 20
    · exact exceptional_path_failure_tendsto_zero hr 20
  simpa only [sum_const_zero] using tendsto_finset_sum univ (fun i _ => h i)

/-- Lemma 3.2, with the constant quantified in the order stated by the paper. -/
theorem lemma32 : Lemma32 := by
  intro r hr
  exact ⟨20, by norm_num, small_separated_exceptional_set hr⟩
end LooseHamilton
