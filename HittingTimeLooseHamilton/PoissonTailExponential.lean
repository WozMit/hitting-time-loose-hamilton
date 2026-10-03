module

public import Mathlib.Probability.Distributions.Poisson.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic

public section
noncomputable section
namespace LooseHamilton
/-- A Poisson upper-tail Chernoff bound with exponential tilt one. -/
theorem poisson_tail_exponential (μ : ℝ) (hμ : 0 ≤ μ) (k : ℕ) :
    1 - Real.exp (-μ) * ∑ j ∈ Finset.range k, μ ^ j / (j.factorial : ℝ) ≤
      Real.exp (μ * (Real.exp 1 - 1) - k) := by
  let f : ℕ → ℝ := fun j => μ ^ j / (j.factorial : ℝ)
  let g : ℕ → ℝ := fun j => (μ * Real.exp 1) ^ j / (j.factorial : ℝ)
  have hf : HasSum f (Real.exp μ) := by
    simpa only [Real.exp_eq_exp_ℝ] using NormedSpace.expSeries_div_hasSum_exp μ
  have hg : HasSum g (Real.exp (μ * Real.exp 1)) := by
    simpa only [g, Real.exp_eq_exp_ℝ] using NormedSpace.expSeries_div_hasSum_exp (μ * Real.exp 1)
  have hfs : Summable (fun j => f (j + k)) := hf.summable.comp_injective
    (fun a b h => Nat.add_right_cancel h)
  have hgs : Summable (fun j => g (j + k)) := hg.summable.comp_injective
    (fun a b h => Nat.add_right_cancel h)
  have hpoint (j : ℕ) : f (j + k) ≤ Real.exp (-(k : ℝ)) * g (j + k) := by
    have he : 1 ≤ Real.exp (-(k : ℝ)) * (Real.exp 1) ^ (j + k) := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]
      apply Real.one_le_exp_iff.mpr
      push_cast
      simp only [mul_one]
      have : (0 : ℝ) ≤ j := Nat.cast_nonneg j
      linarith
    dsimp [f, g]
    rw [mul_pow]
    have hp : 0 ≤ μ ^ (j + k) / ((j + k).factorial : ℝ) := by positivity
    calc
      _ = (μ ^ (j + k) / ((j + k).factorial : ℝ)) * 1 := by ring
      _ ≤ (μ ^ (j + k) / ((j + k).factorial : ℝ)) *
          (Real.exp (-(k : ℝ)) * (Real.exp 1) ^ (j + k)) := mul_le_mul_of_nonneg_left he hp
      _ = _ := by ring
  have hb : (∑' j, f (j + k)) ≤ Real.exp (-(k : ℝ)) * Real.exp (μ * Real.exp 1) := by
    calc
      (∑' j, f (j + k)) ≤ ∑' j, Real.exp (-(k : ℝ)) * g (j + k) :=
        hfs.tsum_le_tsum hpoint (hgs.mul_left _)
      _ = Real.exp (-(k : ℝ)) * ∑' j, g (j + k) := tsum_mul_left
      _ ≤ Real.exp (-(k : ℝ)) * Real.exp (μ * Real.exp 1) := by
        apply mul_le_mul_of_nonneg_left _ (Real.exp_nonneg _)
        have hsplit := hg.summable.sum_add_tsum_nat_add k
        rw [hg.tsum_eq] at hsplit
        have hn : 0 ≤ ∑ j ∈ Finset.range k, g j := Finset.sum_nonneg (fun j _ => by dsimp [g]; positivity)
        linarith
  have hsplit := hf.summable.sum_add_tsum_nat_add k
  rw [hf.tsum_eq] at hsplit
  have hone : Real.exp (-μ) * Real.exp μ = 1 := by rw [← Real.exp_add]; simp
  have hid : 1 - Real.exp (-μ) * ∑ j ∈ Finset.range k, f j =
      Real.exp (-μ) * ∑' j, f (j + k) := by rw [← hsplit] at hone; nlinarith
  change 1 - Real.exp (-μ) * ∑ j ∈ Finset.range k, f j ≤ _
  rw [hid]
  calc
    _ ≤ Real.exp (-μ) * (Real.exp (-(k : ℝ)) * Real.exp (μ * Real.exp 1)) :=
      mul_le_mul_of_nonneg_left hb (Real.exp_nonneg _)
    _ = _ := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
end LooseHamilton
