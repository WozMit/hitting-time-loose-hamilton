module

public import HittingTimeLooseHamilton.KahnLaw
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
public import Mathlib.Tactic

public section

noncomputable section
namespace LooseHamilton.StoppedExponential
open Finset
variable {Ω : Type*} [Fintype Ω]

/-- The elementary bounded-difference MGF estimate, with a nonnegative predictable weight.
Only the weighted conditional mean-zero identity is needed. -/
theorem weighted_mgf (p : FiniteEntropy.Law Ω) (d f : Ω → ℝ) (b lam : ℝ)
    (hb : 0 ≤ b) (hf : ∀ ω, 0 ≤ f ω) (hd : ∀ ω, |d ω| ≤ b)
    (hz : ∑ ω, p.mass ω * f ω * d ω = 0) :
    ∑ ω, p.mass ω * f ω * Real.exp (lam * d ω) ≤
      (∑ ω, p.mass ω * f ω) * Real.exp (lam ^ 2 * b ^ 2 / 2) := by
  by_cases hzero : b = 0
  · have hd0 : ∀ ω, d ω = 0 := fun ω => abs_eq_zero.mp (le_antisymm (by simpa [hzero] using hd ω) (abs_nonneg _))
    simp [hzero, hd0]
  have hb' : 0 < b := lt_of_le_of_ne hb (Ne.symm hzero)
  have hpoint (ω : Ω) : Real.exp (lam * d ω) ≤
      Real.cosh (lam*b) + d ω / b * Real.sinh (lam*b) := by
    have ha : |d ω / b| ≤ 1 := by rw [abs_div, abs_of_pos hb']; exact (div_le_one hb').mpr (hd ω)
    convert Real.exp_mul_le_cosh_add_mul_sinh ha (lam*b) using 1 <;> field_simp <;> ring
  calc
    _ ≤ ∑ ω, p.mass ω * f ω * (Real.cosh (lam*b) + d ω / b * Real.sinh (lam*b)) :=
      sum_le_sum fun ω _ => mul_le_mul_of_nonneg_left (hpoint ω) (mul_nonneg (p.nonneg ω) (hf ω))
    _ = (∑ ω, p.mass ω*f ω) * Real.cosh (lam*b) := by
      simp_rw [mul_add]
      rw [sum_add_distrib, ← sum_mul]
      have he : (∑ ω, p.mass ω * f ω * (d ω / b * Real.sinh (lam*b))) =
          (∑ ω, p.mass ω*f ω*d ω) / b * Real.sinh (lam*b) := by
        simp_rw [div_mul_eq_mul_div, mul_div_assoc]
        rw [sum_mul]
        apply sum_congr rfl
        intro ω _
        ring
      rw [he, hz]
      simp
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left
      · convert Real.cosh_le_exp_half_sq (lam*b) using 1 <;> ring_nf
      · exact sum_nonneg fun ω _ => mul_nonneg (p.nonneg ω) (hf ω)

end LooseHamilton.StoppedExponential
