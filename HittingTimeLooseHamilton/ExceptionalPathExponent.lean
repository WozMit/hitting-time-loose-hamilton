module

public import HittingTimeLooseHamilton.ExceptionalWindowScales

public section

/-! Converting the two-endpoint Chernoff exponent to a polynomial error. -/
noncomputable section
namespace LooseHamilton
open Filter
open scoped Topology

theorem endpoint_exponential_le_rpow {n : ℕ} (hn : 1 ≤ n) {μ : ℝ}
    (hμ : (196 / 100 : ℝ) * Real.log n ≤ μ) :
    Real.exp (-μ * (1-epsilon) - ((2 * lowerDegreeBase (Fin n) : ℕ) : ℝ) * Real.log epsilon) ≤
      (n : ℝ)^(-2 * exceptionalWindowRate) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hlog : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast hn)
  have hfloor : (lowerDegreeBase (Fin n) : ℝ) ≤ epsilon * Real.log n := by
    unfold lowerDegreeBase
    rw [Fintype.card_fin]
    exact Nat.floor_le (mul_nonneg (by norm_num [epsilon]) hlog)
  have hq : Real.log epsilon ≤ 0 := Real.log_nonpos (by norm_num [epsilon]) (by norm_num [epsilon])
  have hm := mul_le_mul_of_nonneg_right hμ (show 0 ≤ 1-epsilon by norm_num [epsilon])
  have hf := mul_le_mul_of_nonpos_right hfloor hq
  rw [Real.rpow_def_of_pos hnpos]
  apply Real.exp_le_exp.mpr
  simp only [Nat.cast_mul, Nat.cast_ofNat]
  unfold exceptionalWindowRate
  nlinarith

/-- The finite path union bound vanishes for each fixed length. -/
theorem exceptional_window_path_error_tendsto_zero (r t : ℕ) :
    Tendsto (fun n : ℕ => (2 * (r : ℝ))^t *
      ((n : ℝ)^(1-2*exceptionalWindowRate) * (Real.log n)^t)) atTop (𝓝 0) := by
  have h := (tendsto_nat_rpow_mul_log_pow (a := 1-2*exceptionalWindowRate)
    (by have := exceptionalWindowRate_gt_92; linarith) t).const_mul ((2 * (r : ℝ))^t)
  simpa only [mul_zero] using h
end LooseHamilton
