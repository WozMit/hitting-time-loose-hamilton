module

public import HittingTimeLooseHamilton.ExceptionalSetModels
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Analysis.Complex.ExponentialBounds

public section

/-! Numerical rate and vanishing errors used for the exceptional set. -/
noncomputable section
namespace LooseHamilton
open Filter

/-- The lower-tail exponent at the manuscript's fixed degree fraction. -/
@[expose] def exceptionalDegreeRate : ℝ := 1 - epsilon + epsilon * Real.log epsilon

theorem log_hundred_lt_five : Real.log 100 < 5 := by
  apply (Real.log_lt_iff_lt_exp (by norm_num : (0 : ℝ) < 100)).mpr
  have he : (8 / 3 : ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have hp : (8 / 3 : ℝ) ^ 5 < (Real.exp 1) ^ 5 := by gcongr
  have hexp : Real.exp (5 : ℝ) = (Real.exp 1) ^ 5 := by
    simpa using (Real.exp_nat_mul (1 : ℝ) 5)
  rw [hexp]
  norm_num at hp ⊢
  linarith

/-- In particular the tail exponent exceeds 11/12 with a fixed positive margin. -/
theorem exceptionalDegreeRate_gt_94 : (94 / 100 : ℝ) < exceptionalDegreeRate := by
  have hl : Real.log epsilon = - Real.log 100 := by
    rw [epsilon,Real.log_div (by norm_num) (by norm_num),Real.log_one,zero_sub]
  unfold exceptionalDegreeRate
  rw [hl,epsilon]
  have h := log_hundred_lt_five
  linarith

theorem exceptionalDegreeRate_gt_eleven_twelfths : (11 / 12 : ℝ) < exceptionalDegreeRate := by
  have h := exceptionalDegreeRate_gt_94
  linarith

/-- The integer exceptional-degree threshold is eventually at least one. -/
theorem lowerDegreeBase_eventually_pos : ∀ᶠ n : ℕ in atTop,
    1 ≤ lowerDegreeBase (Fin n) := by
  have hl : ∀ᶠ n : ℕ in atTop, (100 : ℝ) ≤ Real.log n :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop _)
  filter_upwards [hl] with n hn
  rw [lowerDegreeBase,Fintype.card_fin,Nat.one_le_floor_iff]
  dsimp [epsilon]
  linarith

/-- Any fixed power of log is dominated by any negative polynomial power. -/
theorem tendsto_nat_rpow_mul_log_pow {a : ℝ} (ha : a < 0) (t : ℕ) :
    Tendsto (fun n : ℕ => (n : ℝ) ^ a * (Real.log n) ^ t) atTop (nhds 0) := by
  have h := (isLittleO_log_rpow_rpow_atTop (t : ℝ) (s := -a)
    (neg_pos.mpr ha)).tendsto_div_nhds_zero
  have hn := h.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  convert hn using 1
  ext n
  change (n : ℝ) ^ a * (Real.log n) ^ t = (Real.log n) ^ (t : ℝ) / (n : ℝ) ^ (-a)
  rw [Real.rpow_natCast,Real.rpow_neg (Nat.cast_nonneg n),div_inv_eq_mul,mul_comm]

/-- Ratios of unequal polynomial powers vanish in the required direction. -/
theorem tendsto_nat_rpow_ratio {a b : ℝ} (hab : a < b) :
    Tendsto (fun n : ℕ => (n : ℝ) ^ a / (n : ℝ) ^ b) atTop (nhds 0) := by
  have h := (tendsto_rpow_neg_atTop (sub_pos.mpr hab)).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  apply h.congr'
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  change (n : ℝ) ^ (-(b-a)) = (n : ℝ) ^ a / (n : ℝ) ^ b
  rw [show -(b-a) = a-b by ring, Real.rpow_sub hnpos]

/-- The expectation bound for the exceptional-set size is negligible relative
 to the stated n^(1/12) threshold. -/
theorem exceptional_size_error_tendsto_zero :
    Tendsto (fun n : ℕ => (n : ℝ) ^ (1 - exceptionalDegreeRate) /
      (n : ℝ) ^ (1 / 12 : ℝ)) atTop (nhds 0) := by
  apply tendsto_nat_rpow_ratio
  have h := exceptionalDegreeRate_gt_eleven_twelfths
  linarith

/-- The paired low-degree bound absorbs every bounded-length path's logarithmic factor. -/
theorem exceptional_path_error_tendsto_zero (t : ℕ) :
    Tendsto (fun n : ℕ => (n : ℝ) ^ (1 - 2 * exceptionalDegreeRate) *
      (Real.log n) ^ t) atTop (nhds 0) := by
  apply tendsto_nat_rpow_mul_log_pow
  have h := exceptionalDegreeRate_gt_94
  linarith
end LooseHamilton
