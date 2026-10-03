module

public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Tactic

public section

namespace LooseHamilton.StoppedCounting
/-- The quadratic logarithmic remainder used at every active deletion. -/
theorem neg_log_one_sub_le {q : ℝ} (hq0 : 0 ≤ q) (hq : q ≤ 1 / 2) :
    -Real.log (1 - q) ≤ q + q ^ 2 := by
  let f : ℝ → ℝ := fun x => Real.log (1-x) + x + x^2
  have hd (x : ℝ) (hx : x ∈ Set.Icc (0:ℝ) (1/2)) :
      HasDerivAt f (-1 / (1-x) + 1 + 2*x) x := by
    have hn : 1-x ≠ 0 := by linarith [hx.2]
    convert ((((hasDerivAt_id x).const_sub 1).log hn).add (hasDerivAt_id x)).add
      ((hasDerivAt_id x).pow 2) using 1 <;> first | rfl | simp [f]
  have hm : MonotoneOn f (Set.Icc (0:ℝ) (1/2)) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
    · intro x hx; exact (hd x hx).continuousAt.continuousWithinAt
    · intro x hx; exact (hd x (interior_subset hx)).differentiableAt.differentiableWithinAt
    · intro x hx
      have hx' := interior_subset hx
      rw [(hd x hx').deriv]
      have hn : 0 < 1-x := by linarith [hx'.2]
      have ht : 0 ≤ x * (1-2*x) := mul_nonneg hx'.1 (by linarith [hx'.2])
      apply (mul_nonneg_iff_of_pos_right hn).mp
      field_simp
      nlinarith
  have hh := hm (by norm_num) ⟨hq0,hq⟩ hq0
  dsimp [f] at hh
  simp only [sub_zero, Real.log_one, zero_add, zero_pow, OfNat.ofNat_ne_zero, add_zero] at hh
  linarith
end LooseHamilton.StoppedCounting
