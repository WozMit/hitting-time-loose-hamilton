module

public import HittingTimeLooseHamilton.WindowMeanAsymptotics
public import HittingTimeLooseHamilton.PairDegreeAsymptotic

public section
noncomputable section
namespace LooseHamilton
open Filter

/-- Fraction of edges accounted for by the sample and a single vertex star. -/
@[expose] def isolationSamplingLoad (r : ℕ) (m : ℕ → ℕ) (n : ℕ) : ℝ :=
  ((m n : ℝ) + ((n-1).choose (r-1) : ℝ)) / (n.choose r : ℝ)

lemma sample_log_div_choose_tendsto_zero {r : ℕ} (hr : 2 ≤ r) {m : ℕ → ℕ} {c : ℝ}
    (hm : Tendsto (fun n => (m n : ℝ) / ((n : ℝ) * Real.log n)) atTop (nhds c)) :
    Tendsto (fun n => (m n : ℝ) * Real.log n / (n.choose r : ℝ)) atTop (nhds 0) := by
  have hr' : (1 : ℝ) - r < 0 := by exact_mod_cast (show (1 : ℤ) - r < 0 by omega)
  have hs := tendsto_nat_rpow_mul_log_pow hr' 2
  have hnum : Tendsto (fun n => (m n : ℝ) * Real.log n / (n : ℝ)^r) atTop (nhds 0) := by
    have h := hm.mul hs
    simp only [mul_zero] at h
    apply h.congr'
    filter_upwards [eventually_ge_atTop (2 : ℕ)] with n hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hl : Real.log n ≠ 0 := ne_of_gt (Real.log_pos (by exact_mod_cast (show 1 < n by omega)))
    rw [Real.rpow_sub hn0,Real.rpow_one,Real.rpow_natCast]
    field_simp
    <;> ring
  have hden := normalized_nat_choose_tendsto r
  have h := hnum.div hden (show (1 : ℝ)/(r.factorial : ℝ) ≠ 0 by positivity)
  simp only [zero_div] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hpow : (n : ℝ)^r ≠ 0 := pow_ne_zero _ hn0
  exact div_div_div_cancel_right₀ hpow _ _

lemma star_log_div_choose_tendsto_zero {r : ℕ} (hr : 1 ≤ r) :
    Tendsto (fun n : ℕ => ((n-1).choose (r-1) : ℝ) * Real.log n / (n.choose r : ℝ))
      atTop (nhds 0) := by
  have hlog : Tendsto (fun n : ℕ => Real.log n / (n : ℝ)) atTop (nhds 0) := by
    simpa [Function.comp_def, sub_eq_add_neg] using (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))
  have h := hlog.const_mul (r : ℝ)
  simp only [mul_zero] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop r] with n hn
  calc
    _ = (((n-1).choose (r-1) : ℝ) / (n.choose r : ℝ)) * Real.log n := by
      rw [vertex_incidence_ratio hr hn]; ring
    _ = _ := by ring

lemma isolationSamplingLoad_log_tendsto_zero {r : ℕ} (hr : 2 ≤ r) {m : ℕ → ℕ} {c : ℝ}
    (hm : Tendsto (fun n => (m n : ℝ) / ((n : ℝ) * Real.log n)) atTop (nhds c)) :
    Tendsto (fun n => isolationSamplingLoad r m n * Real.log n) atTop (nhds 0) := by
  have h := (sample_log_div_choose_tendsto_zero hr hm).add
    (star_log_div_choose_tendsto_zero (show 1 ≤ r by omega))
  simp only [add_zero] at h
  convert h using 1
  ext n
  unfold isolationSamplingLoad
  ring

lemma isolationSamplingLoad_tendsto_zero {r : ℕ} (hr : 2 ≤ r) {m : ℕ → ℕ} {c : ℝ}
    (hm : Tendsto (fun n => (m n : ℝ) / ((n : ℝ) * Real.log n)) atTop (nhds c)) :
    Tendsto (isolationSamplingLoad r m) atTop (nhds 0) := by
  have h := (isolationSamplingLoad_log_tendsto_zero hr hm).mul
    (tendsto_inv_atTop_zero.comp (Real.tendsto_log_atTop.comp
      (tendsto_natCast_atTop_atTop (R := ℝ))))
  simp only [mul_zero] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop (2 : ℕ)] with n hn
  have hl : Real.log n ≠ 0 := ne_of_gt (Real.log_pos (by exact_mod_cast (show 1 < n by omega)))
  exact mul_inv_cancel_right₀ hl _

lemma sample_add_star_lt_choose_eventually {r : ℕ} (hr : 2 ≤ r) {m : ℕ → ℕ} {c : ℝ}
    (hm : Tendsto (fun n => (m n : ℝ) / ((n : ℝ) * Real.log n)) atTop (nhds c)) :
    ∀ᶠ n : ℕ in atTop, m n + (n-1).choose (r-1) < n.choose r := by
  have h := (isolationSamplingLoad_tendsto_zero hr hm).eventually
    (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [h,eventually_ge_atTop r] with n hn hnr
  have hN : (0 : ℝ) < n.choose r := by exact_mod_cast Nat.choose_pos hnr
  have hs := (div_lt_one hN).mp hn
  exact_mod_cast hs

lemma mean_mul_load_tendsto_zero {r : ℕ} (hr : 2 ≤ r) {m : ℕ → ℕ} {c : ℝ}
    (hm : Tendsto (fun n => (m n : ℝ) / ((n : ℝ) * Real.log n)) atTop (nhds c)) :
    Tendsto (fun n => isolationMean r m n * isolationSamplingLoad r m n) atTop (nhds 0) := by
  have h := (isolationMean_ratio_tendsto (show 1 ≤ r by omega) hm).mul
    (isolationSamplingLoad_log_tendsto_zero hr hm)
  simp only [mul_zero] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop (2 : ℕ)] with n hn
  have hl : Real.log n ≠ 0 := ne_of_gt (Real.log_pos (by exact_mod_cast (show 1 < n by omega)))
  field_simp
  <;> ring

lemma pair_mean_tendsto_zero {r : ℕ} (hr : 2 ≤ r) {m : ℕ → ℕ} {c : ℝ}
    (hm : Tendsto (fun n => (m n : ℝ) / ((n : ℝ) * Real.log n)) atTop (nhds c)) :
    Tendsto (fun n => ((n-2).choose (r-2) : ℝ) * (m n : ℝ) / (n.choose r : ℝ))
      atTop (nhds 0) := by
  have hlog : Tendsto (fun n : ℕ => Real.log n / ((n : ℝ)-1)) atTop (nhds 0) := by
    simpa [Function.comp_def, sub_eq_add_neg] using (Real.tendsto_pow_log_div_mul_add_atTop 1 (-1) 1 one_ne_zero).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))
  have h := (hm.mul hlog).const_mul ((r : ℝ)*(r-1))
  simp only [mul_zero] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop (max r 2)] with n hn
  have hnr : r ≤ n := (le_max_left _ _).trans hn
  have hn2 : 2 ≤ n := (le_max_right _ _).trans hn
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hn1 : (n : ℝ)-1 ≠ 0 := by
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn2
    linarith
  have hl : Real.log n ≠ 0 := ne_of_gt (Real.log_pos (by exact_mod_cast (show 1 < n by omega)))
  calc
    _ = (((n-2).choose (r-2) : ℝ)/(n.choose r : ℝ)) * (m n : ℝ) := by
      rw [pair_incidence_ratio hr hnr]
      field_simp
      <;> ring
    _ = _ := by ring
end LooseHamilton
