module

public import HittingTimeLooseHamilton.ExceptionalSetAsymptotics
public import HittingTimeLooseHamilton.NormalizationAsymptotic

public section

/-! Deterministic scales for a constant-relative bracket around the isolated-vertex
threshold. These results do not assert that the random stopping time lies inside it. -/
noncomputable section
namespace LooseHamilton
open Filter

/-- The lower comparison time, rounded down. -/
@[expose] def exceptionalWindowLo (r n : ℕ) : ℕ :=
  Nat.floor ((99 / 100 : ℝ) / r * ((n : ℝ) * Real.log n))

/-- The upper comparison time, rounded up. -/
@[expose] def exceptionalWindowHi (r n : ℕ) : ℕ :=
  Nat.ceil ((101 / 100 : ℝ) / r * ((n : ℝ) * Real.log n))

/-- A conservative exponent allowing the early mean to be 0.98 log n. -/
@[expose] def exceptionalWindowRate : ℝ :=
  (98 / 100 : ℝ) * (1 - epsilon) + epsilon * Real.log epsilon

theorem exceptionalWindowRate_gt_92 : (92 / 100 : ℝ) < exceptionalWindowRate := by
  have h := exceptionalDegreeRate_gt_94
  unfold exceptionalWindowRate exceptionalDegreeRate at *
  rw [epsilon] at *
  linarith

theorem exceptionalWindowRate_gt_eleven_twelfths :
    (11 / 12 : ℝ) < exceptionalWindowRate := by
  have h := exceptionalWindowRate_gt_92
  linarith

theorem tendsto_nat_mul_log_atTop :
    Tendsto (fun n : ℕ => (n : ℝ) * Real.log n) atTop atTop :=
  tendsto_natCast_atTop_atTop.atTop_mul_atTop₀
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)

theorem exceptionalWindowLo_ratio_tendsto (r : ℕ) :
    Tendsto (fun n : ℕ => (exceptionalWindowLo r n : ℝ) / ((n : ℝ) * Real.log n))
      atTop (nhds ((99 / 100 : ℝ) / r)) := by
  exact (tendsto_nat_floor_mul_div_atTop (show (0 : ℝ) ≤ (99 / 100 : ℝ) / r by positivity)).comp
    tendsto_nat_mul_log_atTop

theorem exceptionalWindowHi_ratio_tendsto (r : ℕ) :
    Tendsto (fun n : ℕ => (exceptionalWindowHi r n : ℝ) / ((n : ℝ) * Real.log n))
      atTop (nhds ((101 / 100 : ℝ) / r)) := by
  exact (tendsto_nat_ceil_mul_div_atTop (show (0 : ℝ) ≤ (101 / 100 : ℝ) / r by positivity)).comp
    tendsto_nat_mul_log_atTop

/-- Rounding preserves the ordering for every n, including the zero cases. -/
theorem exceptionalWindowLo_le_hi (r n : ℕ) : exceptionalWindowLo r n ≤ exceptionalWindowHi r n := by
  have hx : (0 : ℝ) ≤ (99 / 100 : ℝ) / r * ((n : ℝ) * Real.log n) := by positivity
  have hxy : (99 / 100 : ℝ) / r * ((n : ℝ) * Real.log n) ≤
      (101 / 100 : ℝ) / r * ((n : ℝ) * Real.log n) := by
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    exact div_le_div_of_nonneg_right (by norm_num) (Nat.cast_nonneg r)
  exact_mod_cast (Nat.floor_le hx).trans (hxy.trans (Nat.le_ceil _))

theorem normalized_nat_choose_tendsto (r : ℕ) :
    Tendsto (fun n : ℕ => (n.choose r : ℝ) / (n : ℝ)^r)
      atTop (nhds (1 / (r.factorial : ℝ))) := by
  have hratio : Tendsto (fun n : ℕ => (n : ℝ) / n) atTop (nhds (1 : ℝ)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
    simp [hn']
  simpa using normalized_choose_tendsto (A := id) (N := id) tendsto_id tendsto_id hratio r

theorem nat_mul_log_div_pow_tendsto_zero {r : ℕ} (hr : 2 ≤ r) :
    Tendsto (fun n : ℕ => ((n : ℝ) * Real.log n) / (n : ℝ)^r) atTop (nhds 0) := by
  have hr' : (1 : ℝ) - r < 0 := by exact_mod_cast (show (1 : ℤ) - r < 0 by omega)
  have h := tendsto_nat_rpow_mul_log_pow hr' 1
  apply h.congr'
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  have hn' : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  rw [Real.rpow_sub hn',Real.rpow_one,Real.rpow_natCast,pow_one]
  ring

theorem exceptionalWindowHi_div_pow_tendsto_zero {r : ℕ} (hr : 2 ≤ r) :
    Tendsto (fun n : ℕ => (exceptionalWindowHi r n : ℝ) / (n : ℝ)^r)
      atTop (nhds 0) := by
  have h := (exceptionalWindowHi_ratio_tendsto r).mul (nat_mul_log_div_pow_tendsto_zero hr)
  simp only [mul_zero] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop (2 : ℕ)] with n hn
  have hn' : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
  have hne : (n : ℝ) * Real.log n ≠ 0 := ne_of_gt (mul_pos (by linarith) (Real.log_pos hn'))
  exact div_mul_div_cancel₀ hne

/-- Both comparison times are eventually within the finite edge-order process. -/
theorem exceptionalWindow_times_le_complete_eventually {r : ℕ} (hr : 3 ≤ r) :
    ∀ᶠ n : ℕ in atTop, exceptionalWindowLo r n ≤ n.choose r ∧
      exceptionalWindowHi r n ≤ n.choose r := by
  have hpos : (0 : ℝ) < 1 / (2 * (r.factorial : ℝ)) := by positivity
  have hhi := (exceptionalWindowHi_div_pow_tendsto_zero (show 2 ≤ r by omega)).eventually
    (gt_mem_nhds hpos)
  have hchoose := (normalized_nat_choose_tendsto r).eventually
    (lt_mem_nhds (show (1 : ℝ) / (2 * (r.factorial : ℝ)) < 1 / (r.factorial : ℝ) by
      have hp : (0 : ℝ) < r.factorial := by positivity
      exact one_div_lt_one_div_of_lt hp (by linarith)))
  filter_upwards [hhi,hchoose,eventually_ge_atTop (1 : ℕ)] with n hhi hchoose hn
  have hp : (0 : ℝ) < (n : ℝ)^r := by
    apply pow_pos
    exact_mod_cast (show 0 < n by omega)
  have hh : (exceptionalWindowHi r n : ℝ) < (n.choose r : ℝ) :=
    (div_lt_div_iff_of_pos_right hp).mp (hhi.trans hchoose)
  have hh' : exceptionalWindowHi r n ≤ n.choose r := Nat.le_of_lt (by exact_mod_cast hh)
  exact ⟨(exceptionalWindowLo_le_hi r n).trans hh',hh'⟩

/-- The conservative early-window exponent still suffices for the size bound. -/
theorem exceptional_window_size_error_tendsto_zero :
    Tendsto (fun n : ℕ => (n : ℝ) ^ (1 - exceptionalWindowRate) /
      (n : ℝ) ^ (1 / 12 : ℝ)) atTop (nhds 0) := by
  apply tendsto_nat_rpow_ratio
  have h := exceptionalWindowRate_gt_eleven_twelfths
  linarith
end LooseHamilton
