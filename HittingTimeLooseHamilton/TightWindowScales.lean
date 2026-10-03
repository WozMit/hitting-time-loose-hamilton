module

public import HittingTimeLooseHamilton.WindowIsolationAsymptotics

public section

/-! The logarithmically tightened comparison window used for the conditioned core. -/
noncomputable section
namespace LooseHamilton
open Filter

/-- The real comparison scale before rounding, with a fixed log-log offset. -/
@[expose] def coreWindowScale (r : ℕ) (a : ℝ) (n : ℕ) : ℝ :=
  (n : ℝ) / r * (Real.log n + a * Real.log (Real.log n))

@[expose] def coreWindowLo (r n : ℕ) : ℕ := Nat.floor (coreWindowScale r (-2) n)
@[expose] def coreWindowHi (r n : ℕ) : ℕ := Nat.ceil (coreWindowScale r 2 n)

lemma coreWindowScale_ratio_tendsto (r : ℕ) (a : ℝ) :
    Tendsto (fun n => coreWindowScale r a n / ((n : ℝ) * Real.log n))
      atTop (nhds (1 / (r : ℝ))) := by
  have hlog : Tendsto (fun n : ℕ => Real.log (Real.log n) / Real.log n) atTop (nhds 0) := by
    exact Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp
      (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ)))
  have h := ((hlog.const_mul a).const_add 1).const_mul (1 / (r : ℝ))
  simp only [mul_zero,add_zero,mul_one] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop (2 : ℕ)] with n hn
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hl : Real.log n ≠ 0 := ne_of_gt (Real.log_pos (by exact_mod_cast (show 1 < n by omega)))
  unfold coreWindowScale
  by_cases hr0 : (r : ℝ) = 0
  · simp [hr0]
  · field_simp [hn0,hl,hr0]
    <;> ring

lemma core_scale_tendsto_atTop {f : ℕ → ℝ} {c : ℝ} (hc : 0 < c)
    (hf : Tendsto (fun n => f n / ((n : ℝ)*Real.log n)) atTop (nhds c)) :
    Tendsto f atTop atTop := by
  apply (hf.pos_mul_atTop hc tendsto_nat_mul_log_atTop).congr'
  filter_upwards [eventually_ge_atTop (2 : ℕ)] with n hn
  have hne : (n : ℝ)*Real.log n ≠ 0 := ne_of_gt
    (mul_pos (by exact_mod_cast (show 0 < n by omega))
      (Real.log_pos (by exact_mod_cast (show 1 < n by omega))))
  exact div_mul_cancel₀ _ hne

lemma core_rounding_ratio {f : ℕ → ℝ} {c : ℝ} (hc : 0 < c)
    (hf : Tendsto (fun n => f n / ((n : ℝ)*Real.log n)) atTop (nhds c)) :
    Tendsto (fun n => (Nat.floor (f n) : ℝ) / ((n : ℝ)*Real.log n)) atTop (nhds c) ∧
    Tendsto (fun n => (Nat.ceil (f n) : ℝ) / ((n : ℝ)*Real.log n)) atTop (nhds c) := by
  have htop := core_scale_tendsto_atTop hc hf
  have hpos := htop.eventually (eventually_gt_atTop 0)
  constructor
  · have h := (tendsto_nat_floor_div_atTop.comp htop).mul hf
    simp only [one_mul] at h
    apply h.congr'
    filter_upwards [hpos] with n hn
    exact div_mul_div_cancel₀ (ne_of_gt hn)
  · have h := (tendsto_nat_ceil_div_atTop.comp htop).mul hf
    simp only [one_mul] at h
    apply h.congr'
    filter_upwards [hpos] with n hn
    exact div_mul_div_cancel₀ (ne_of_gt hn)

lemma coreWindowLo_ratio_tendsto {r : ℕ} (hr : 1 ≤ r) :
    Tendsto (fun n => (coreWindowLo r n : ℝ) / ((n : ℝ)*Real.log n))
      atTop (nhds (1 / (r : ℝ))) := by
  have hr0 : (0 : ℝ) < r := by exact_mod_cast (show 0 < r by omega)
  exact (core_rounding_ratio (one_div_pos.mpr hr0) (coreWindowScale_ratio_tendsto r (-2))).1

lemma coreWindowHi_ratio_tendsto {r : ℕ} (hr : 1 ≤ r) :
    Tendsto (fun n => (coreWindowHi r n : ℝ) / ((n : ℝ)*Real.log n))
      atTop (nhds (1 / (r : ℝ))) := by
  have hr0 : (0 : ℝ) < r := by exact_mod_cast (show 0 < r by omega)
  exact (core_rounding_ratio (one_div_pos.mpr hr0) (coreWindowScale_ratio_tendsto r 2)).2

lemma coreWindowScale_eventually_nonneg {r : ℕ} (hr : 1 ≤ r) (a : ℝ) :
    ∀ᶠ n : ℕ in atTop, 0 ≤ coreWindowScale r a n := by
  have hr0 : (0 : ℝ) < r := by exact_mod_cast (show 0 < r by omega)
  exact (core_scale_tendsto_atTop (one_div_pos.mpr hr0)
    (coreWindowScale_ratio_tendsto r a)).eventually (eventually_ge_atTop 0)

lemma coreWindowLo_le_hi_eventually {r : ℕ} (hr : 1 ≤ r) :
    ∀ᶠ n : ℕ in atTop, coreWindowLo r n ≤ coreWindowHi r n := by
  have hlog := (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))).eventually
    (eventually_ge_atTop 1)
  filter_upwards [coreWindowScale_eventually_nonneg hr (-2),hlog] with n hn hl
  have hll : 0 ≤ Real.log (Real.log n) := Real.log_nonneg hl
  have hscale : coreWindowScale r (-2) n ≤ coreWindowScale r 2 n := by
    unfold coreWindowScale
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    linarith
  exact Nat.cast_le.mp ((Nat.floor_le hn).trans (hscale.trans (Nat.le_ceil _)))

lemma coreWindowLo_gap_eventually {r : ℕ} (hr : 3 ≤ r) :
    ∀ᶠ n : ℕ in atTop, coreWindowLo r n + (n-1).choose (r-1) < n.choose r :=
  sample_add_star_lt_choose_eventually (by omega) (coreWindowLo_ratio_tendsto (by omega))

lemma coreWindowHi_valid_eventually {r : ℕ} (hr : 3 ≤ r) :
    ∀ᶠ n : ℕ in atTop, coreWindowHi r n ≤ n.choose r := by
  filter_upwards [sample_add_star_lt_choose_eventually (show 2 ≤ r by omega)
    (coreWindowHi_ratio_tendsto (by omega : 1 ≤ r))] with n hn
  omega
end LooseHamilton
