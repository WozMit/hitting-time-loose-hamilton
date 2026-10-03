module

public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Data.Real.Basic
public import Mathlib.Tactic

public section

noncomputable section
open scoped BigOperators
namespace LooseHamilton.StoppedCounting
/-- The deterministic square-increment budget in the manuscript. -/
@[expose] def variance (C0 : ℝ) (k M K : ℕ) : ℝ :=
  ∑ j ∈ Finset.Ioc M K, (C0 * k / j) ^ 2

theorem variance_nonneg (C0 : ℝ) (k M K : ℕ) : 0 ≤ variance C0 k M K :=
  Finset.sum_nonneg (fun _ _ => sq_nonneg _)

@[simp] theorem variance_zero_card (C0 : ℝ) (M K : ℕ) : variance C0 0 M K = 0 := by
  simp [variance]

@[simp] theorem variance_no_steps (C0 : ℝ) (k M : ℕ) : variance C0 k M M = 0 := by
  simp [variance]

/-- Reverse the index from current host size to number of deletions made. -/
theorem variance_eq_sum_steps (C0 : ℝ) (k M K : ℕ) (hMK : M ≤ K) :
    variance C0 k M K = ∑ t ∈ Finset.range (K-M), (C0 * k / ((K-t : ℕ) : ℝ)) ^ 2 := by
  unfold variance
  apply Finset.sum_bij (fun j _ => K-j)
  · intro j hj
    simp only [Finset.mem_Ioc] at hj
    simp only [Finset.mem_range]
    omega
  · intro i hi j hj heq
    simp only [Finset.mem_Ioc] at hi hj
    omega
  · intro t ht
    simp only [Finset.mem_range] at ht
    refine ⟨K-t, ?_, ?_⟩
    · simp only [Finset.mem_Ioc]; omega
    · omega
  · intro j hj
    have hjK := (Finset.mem_Ioc.mp hj).2
    have hn : K-(K-j)=j := by omega
    rw [hn]
end LooseHamilton.StoppedCounting
