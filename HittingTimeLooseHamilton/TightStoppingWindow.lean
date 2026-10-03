module

public import HittingTimeLooseHamilton.TightWindowDensity
public import HittingTimeLooseHamilton.ExceptionalStoppingWindow

public section

/-! The minimum-degree-one stopping time lies in the log n ± 2 log log n window
with probability tending to one, under the original random edge-order process. -/
noncomputable section
namespace LooseHamilton
open Filter

lemma isolationMean_eq_scaled {n r : ℕ} (hr : 1 ≤ r) (hn : r ≤ n) (m : ℕ → ℕ) :
    isolationMean r m n = (r : ℝ) / n * (m n : ℝ) := by
  unfold isolationMean
  calc
    _ = (((n-1).choose (r-1) : ℝ)/(n.choose r : ℝ)) * (m n : ℝ) := by ring
    _ = _ := by rw [vertex_incidence_ratio hr hn]

lemma coreWindowScale_mean {n r : ℕ} (hr : 1 ≤ r) (hn : r ≤ n) (a : ℝ) :
    (r : ℝ) / n * coreWindowScale r a n = Real.log n + a * Real.log (Real.log n) := by
  have hr0 : (r : ℝ) ≠ 0 := by exact_mod_cast (show r ≠ 0 by omega)
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  unfold coreWindowScale
  field_simp
  <;> ring

lemma coreWindowLo_mean_le {n r : ℕ} (hr : 1 ≤ r) (hn : r ≤ n)
    (hs : 0 ≤ coreWindowScale r (-2) n) :
    isolationMean r (coreWindowLo r) n ≤ Real.log n - 2 * Real.log (Real.log n) := by
  rw [isolationMean_eq_scaled hr hn]
  have h := mul_le_mul_of_nonneg_left (Nat.floor_le hs)
    (show (0 : ℝ) ≤ (r : ℝ) / n by positivity)
  simpa only [coreWindowLo,coreWindowScale_mean hr hn,neg_mul,sub_eq_add_neg] using h

lemma coreWindowHi_mean_ge {n r : ℕ} (hr : 1 ≤ r) (hn : r ≤ n) :
    Real.log n + 2 * Real.log (Real.log n) ≤ isolationMean r (coreWindowHi r) n := by
  rw [isolationMean_eq_scaled hr hn]
  have h := mul_le_mul_of_nonneg_left (Nat.le_ceil (coreWindowScale r 2 n))
    (show (0 : ℝ) ≤ (r : ℝ) / n by positivity)
  simpa only [coreWindowHi,coreWindowScale_mean hr hn] using h

lemma core_log_inverse_square_tendsto_zero :
    Tendsto (fun n : ℕ => 1 / (Real.log n)^2) atTop (nhds 0) := by
  have h := (tendsto_inv_atTop_zero.comp (Real.tendsto_log_atTop.comp
    (tendsto_natCast_atTop_atTop (R := ℝ)))).pow 2
  simpa only [zero_pow (by decide : 2 ≠ 0),one_div,inv_pow,Function.comp_def] using h

lemma coreWindowLo_mean_exp_tendsto_zero {r : ℕ} (hr : 1 ≤ r) :
    Tendsto (fun n => Real.exp (isolationMean r (coreWindowLo r) n) / (n : ℝ))
      atTop (nhds 0) := by
  apply squeeze_zero' (Eventually.of_forall (fun n =>
    div_nonneg (Real.exp_pos _).le (Nat.cast_nonneg n))) ?_ core_log_inverse_square_tendsto_zero
  filter_upwards [coreWindowScale_eventually_nonneg hr (-2),eventually_ge_atTop (max r 2)] with n hs hn
  have hnr : r ≤ n := (le_max_left _ _).trans hn
  have hn2 : 2 ≤ n := (le_max_right _ _).trans hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hl : 0 < Real.log n := Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  have he : Real.exp (2 * Real.log (Real.log n)) = (Real.log n)^2 := by
    simpa only [Nat.cast_ofNat, Real.exp_log hl] using (Real.exp_nat_mul (Real.log (Real.log n)) 2)
  calc
    _ ≤ Real.exp (Real.log n - 2 * Real.log (Real.log n)) / (n : ℝ) :=
      div_le_div_of_nonneg_right (Real.exp_le_exp.mpr (coreWindowLo_mean_le hr hnr hs)) hn0.le
    _ = _ := by
      rw [Real.exp_sub,Real.exp_log hn0,he]
      field_simp
      <;> ring

lemma coreWindowLo_exp_tendsto_zero {r : ℕ} (hr : 3 ≤ r) :
    Tendsto (fun n => Real.exp (isolationLowerExponent (Fin n) r (coreWindowLo r n)) /
      (n : ℝ)) atTop (nhds 0) := by
  have hd := isolationLowerExponent_sub_mean_tendsto_zero (show 2 ≤ r by omega)
    (coreWindowLo_ratio_tendsto (by omega : 1 ≤ r))
  have he := Real.continuous_exp.continuousAt.tendsto.comp hd
  have h := he.mul (coreWindowLo_mean_exp_tendsto_zero (by omega : 1 ≤ r))
  simp only [mul_zero] at h
  apply h.congr'
  filter_upwards with n
  dsimp only [Function.comp_def]
  rw [← mul_div_assoc,← Real.exp_add,sub_add_cancel]

lemma coreWindowHi_exp_tendsto_zero {r : ℕ} (hr : 3 ≤ r) :
    Tendsto (fun n : ℕ => (n : ℝ) * Real.exp (-(((n-1).choose (r-1) : ℝ) *
      (coreWindowHi r n : ℝ) / (n.choose r : ℝ)))) atTop (nhds 0) := by
  change Tendsto (fun n : ℕ => (n : ℝ) * Real.exp (-isolationMean r (coreWindowHi r) n)) _ _
  apply squeeze_zero' (Eventually.of_forall (fun n =>
    mul_nonneg (Nat.cast_nonneg n) (Real.exp_pos _).le)) ?_ core_log_inverse_square_tendsto_zero
  filter_upwards [eventually_ge_atTop (max r 2)] with n hn
  have hnr : r ≤ n := (le_max_left _ _).trans hn
  have hn2 : 2 ≤ n := (le_max_right _ _).trans hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hl : 0 < Real.log n := Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  have he : Real.exp (2 * Real.log (Real.log n)) = (Real.log n)^2 := by
    simpa only [Nat.cast_ofNat, Real.exp_log hl] using (Real.exp_nat_mul (Real.log (Real.log n)) 2)
  calc
    _ ≤ (n : ℝ) * Real.exp (-(Real.log n + 2 * Real.log (Real.log n))) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
        (neg_le_neg (coreWindowHi_mean_ge (by omega : 1 ≤ r) hnr))) hn0.le
    _ = _ := by
      rw [Real.exp_neg,Real.exp_add,Real.exp_log hn0,he]
      field_simp
      <;> ring

/-- Failure of the finite tightened stopping bracket. -/
@[expose] def coreStoppingWindowFailure {r n : ℕ} (σ : EdgeOrder (Fin n) r) : Prop :=
  ¬ ∃ t : ℕ, tauOne σ = (t : WithTop ℕ) ∧ coreWindowLo r n ≤ t ∧ t ≤ coreWindowHi r n

/-- The exact original stopping process lies in the tightened window with high probability. -/
theorem core_stopping_window_tendsto_zero {r : ℕ} (hr : 3 ≤ r) :
    Tendsto (fun n => (processLaw (Fin n) r).event coreStoppingWindowFailure) atTop (nhds 0) := by
  have h := exceptional_stopping_window_tendsto_of_scalar (show 2 ≤ r by omega)
    0 (coreWindowLo r) (coreWindowHi r)
    (coreWindowLo_gap_eventually hr) (coreWindowHi_valid_eventually hr)
    (coreWindowLo_exp_tendsto_zero hr)
    (isolation_pair_correction_tendsto_zero (by omega) (coreWindowLo_ratio_tendsto (by omega : 1 ≤ r)))
    (coreWindowHi_exp_tendsto_zero hr)
  exact h
end LooseHamilton
