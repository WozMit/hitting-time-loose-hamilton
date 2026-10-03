module

public import HittingTimeLooseHamilton.WindowSamplingAsymptotics
public import HittingTimeLooseHamilton.IsolatedVertexExponentialBounds

public section
noncomputable section
namespace LooseHamilton
open Filter

lemma isolationLowerExponent_eq_mean_div {r n : ℕ} (m : ℕ → ℕ)
    (hgap : m n + (n-1).choose (r-1) < n.choose r) :
    isolationLowerExponent (Fin n) r (m n) =
      isolationMean r m n / (1 - isolationSamplingLoad r m n) := by
  have hm : m n ≤ n.choose r := by omega
  have hD : (n-1).choose (r-1) ≤ n.choose r - m n := by omega
  have hN : (0 : ℝ) < n.choose r := by exact_mod_cast (show 0 < n.choose r by omega)
  have hsum : (m n : ℝ) + ((n-1).choose (r-1) : ℝ) < (n.choose r : ℝ) := by exact_mod_cast hgap
  have hload : isolationSamplingLoad r m n < 1 := (div_lt_one hN).mpr hsum
  have hne : 1 - isolationSamplingLoad r m n ≠ 0 := ne_of_gt (sub_pos.mpr hload)
  have hden : (n.choose r : ℝ) - (m n : ℝ) - ((n-1).choose (r-1) : ℝ) ≠ 0 := by linarith
  simp only [isolationLowerExponent,Fintype.card_fin,Nat.cast_sub hD,Nat.cast_sub hm]
  unfold isolationMean isolationSamplingLoad
  have hrewrite : 1 - ((m n : ℝ) + ((n-1).choose (r-1) : ℝ)) / (n.choose r : ℝ) =
      ((n.choose r : ℝ) - (m n : ℝ) - ((n-1).choose (r-1) : ℝ)) / (n.choose r : ℝ) := by
    field_simp
    <;> ring
  rw [hrewrite,div_div_div_cancel_right₀ (ne_of_gt hN)]

lemma isolationLowerExponent_sub_mean_tendsto_zero {r : ℕ} (hr : 2 ≤ r)
    {m : ℕ → ℕ} {c : ℝ}
    (hm : Tendsto (fun n => (m n : ℝ) / ((n : ℝ) * Real.log n)) atTop (nhds c)) :
    Tendsto (fun n => isolationLowerExponent (Fin n) r (m n) - isolationMean r m n)
      atTop (nhds 0) := by
  have hden : Tendsto (fun n => 1 - isolationSamplingLoad r m n) atTop (nhds (1 : ℝ)) := by
    simpa using tendsto_const_nhds.sub (isolationSamplingLoad_tendsto_zero hr hm)
  have h := (mean_mul_load_tendsto_zero hr hm).div hden one_ne_zero
  simp only [zero_div] at h
  change Tendsto (fun n => (isolationMean r m n * isolationSamplingLoad r m n) /
    (1 - isolationSamplingLoad r m n)) atTop (nhds 0) at h
  apply h.congr'
  filter_upwards [sample_add_star_lt_choose_eventually hr hm] with n hn
  rw [isolationLowerExponent_eq_mean_div m hn]
  have hN : (0 : ℝ) < n.choose r := by exact_mod_cast (show 0 < n.choose r by omega)
  have hs : (m n : ℝ) + ((n-1).choose (r-1) : ℝ) < (n.choose r : ℝ) := by exact_mod_cast hn
  have hd : 1 - isolationSamplingLoad r m n ≠ 0 := ne_of_gt
    (sub_pos.mpr ((div_lt_one hN).mpr hs))
  field_simp
  <;> ring

lemma isolationLowerExponent_ratio_tendsto {r : ℕ} (hr : 2 ≤ r)
    {m : ℕ → ℕ} {c : ℝ}
    (hm : Tendsto (fun n => (m n : ℝ) / ((n : ℝ) * Real.log n)) atTop (nhds c)) :
    Tendsto (fun n => isolationLowerExponent (Fin n) r (m n) / Real.log n)
      atTop (nhds ((r : ℝ)*c)) := by
  have hdiff := (isolationLowerExponent_sub_mean_tendsto_zero hr hm).mul
    (tendsto_inv_atTop_zero.comp (Real.tendsto_log_atTop.comp
      (tendsto_natCast_atTop_atTop (R := ℝ))))
  have h := (isolationMean_ratio_tendsto (show 1 ≤ r by omega) hm).add hdiff
  simp only [mul_zero,add_zero] at h
  convert h using 1
  ext n
  dsimp only [Function.comp_def]
  ring

lemma pair_support_le_twice_star {n r : ℕ} (hr : 2 ≤ r) (hn : 2 ≤ n) :
    (n-2).choose (r-2) ≤ 2 * (n-1).choose (r-1) := by
  have h : (n-2).choose (r-2) ≤ (n-1).choose (r-1) := by
    rw [show n-1 = (n-2)+1 by omega,show r-1 = (r-2)+1 by omega,Nat.choose_succ_succ]
    omega
  omega

lemma isolationPairExponent_eq {n r : ℕ} (hr : 2 ≤ r) (hn : 2 ≤ n) (m : ℕ → ℕ) :
    isolationPairExponent (Fin n) r (m n) =
      2 * isolationMean r m n - ((n-2).choose (r-2) : ℝ) * (m n : ℝ) / (n.choose r : ℝ) := by
  simp only [isolationPairExponent,Fintype.card_fin,Nat.cast_sub (pair_support_le_twice_star hr hn),
    Nat.cast_mul,Nat.cast_ofNat,isolationMean]
  ring

lemma isolation_pair_correction_tendsto_zero {r : ℕ} (hr : 2 ≤ r)
    {m : ℕ → ℕ} {c : ℝ}
    (hm : Tendsto (fun n => (m n : ℝ) / ((n : ℝ) * Real.log n)) atTop (nhds c)) :
    Tendsto (fun n => 2 * isolationLowerExponent (Fin n) r (m n) -
      isolationPairExponent (Fin n) r (m n)) atTop (nhds 0) := by
  have h := ((isolationLowerExponent_sub_mean_tendsto_zero hr hm).const_mul 2).add
    (pair_mean_tendsto_zero hr hm)
  simp only [mul_zero,add_zero] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop (2 : ℕ)] with n hn
  rw [isolationPairExponent_eq hr hn m]
  ring

/-- A logarithmic exponent strictly below log n yields a negligible diagonal term. -/
lemma exp_div_nat_tendsto_zero_of_log_ratio {A : ℕ → ℝ} {c : ℝ} (hc : c < 1)
    (hA : Tendsto (fun n => A n / Real.log n) atTop (nhds c)) :
    Tendsto (fun n => Real.exp (A n) / (n : ℝ)) atTop (nhds 0) := by
  let d := (c+1)/2
  have hd : c < d := by dsimp [d]; linarith
  have hd1 : d < 1 := by dsimp [d]; linarith
  have hbound := hA.eventually (gt_mem_nhds hd)
  have hlim : Tendsto (fun n : ℕ => (n : ℝ) ^ (d-1)) atTop (nhds 0) := by
    have h := (tendsto_rpow_neg_atTop (sub_pos.mpr hd1)).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))
    simpa only [neg_sub, Function.comp_def] using h
  apply squeeze_zero' (Eventually.of_forall (fun n => div_nonneg (Real.exp_pos _).le (Nat.cast_nonneg n))) ?_ hlim
  filter_upwards [hbound,eventually_ge_atTop (2 : ℕ)] with n hn hn2
  have hn1 : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
  have hn0 : (0 : ℝ) < n := by linarith
  have hlog : 0 < Real.log n := Real.log_pos hn1
  have hAn : A n ≤ d * Real.log n := ((div_lt_iff₀ hlog).mp hn).le
  calc
    _ ≤ Real.exp (d * Real.log n) / (n : ℝ) := div_le_div_of_nonneg_right
      (Real.exp_le_exp.mpr hAn) hn0.le
    _ = _ := by
      rw [Real.rpow_sub hn0,Real.rpow_one,Real.rpow_def_of_pos hn0]
      rw [mul_comm d (Real.log n)]

/-- An exponent strictly above log n makes the first-moment isolation bound vanish. -/
lemma nat_mul_exp_neg_tendsto_zero_of_log_ratio {A : ℕ → ℝ} {c : ℝ} (hc : 1 < c)
    (hA : Tendsto (fun n => A n / Real.log n) atTop (nhds c)) :
    Tendsto (fun n : ℕ => (n : ℝ) * Real.exp (-A n)) atTop (nhds 0) := by
  let d := (c+1)/2
  have hd : d < c := by dsimp [d]; linarith
  have hd1 : 1 < d := by dsimp [d]; linarith
  have hbound := hA.eventually (lt_mem_nhds hd)
  have hlim : Tendsto (fun n : ℕ => (n : ℝ) ^ (1-d)) atTop (nhds 0) := by
    have h := (tendsto_rpow_neg_atTop (sub_pos.mpr hd1)).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))
    simpa only [neg_sub, Function.comp_def] using h
  apply squeeze_zero' (Eventually.of_forall (fun n => mul_nonneg (Nat.cast_nonneg n) (Real.exp_pos _).le)) ?_ hlim
  filter_upwards [hbound,eventually_ge_atTop (2 : ℕ)] with n hn hn2
  have hn1 : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
  have hn0 : (0 : ℝ) < n := by linarith
  have hlog : 0 < Real.log n := Real.log_pos hn1
  have hAn : d * Real.log n ≤ A n := ((lt_div_iff₀ hlog).mp hn).le
  calc
    _ ≤ (n : ℝ) * Real.exp (-(d * Real.log n)) := mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (neg_le_neg hAn)) hn0.le
    _ = _ := by
      rw [Real.exp_neg,Real.rpow_sub hn0,Real.rpow_one,Real.rpow_def_of_pos hn0]
      rw [mul_comm d (Real.log n)]
      rfl

lemma exceptionalWindowLo_gap_eventually {r : ℕ} (hr : 3 ≤ r) :
    ∀ᶠ n : ℕ in atTop, exceptionalWindowLo r n + (n-1).choose (r-1) < n.choose r :=
  sample_add_star_lt_choose_eventually (by omega) (exceptionalWindowLo_ratio_tendsto r)

lemma exceptionalWindowLo_exp_tendsto_zero {r : ℕ} (hr : 3 ≤ r) :
    Tendsto (fun n => Real.exp (isolationLowerExponent (Fin n) r (exceptionalWindowLo r n)) /
      (n : ℝ)) atTop (nhds 0) := by
  have h := isolationLowerExponent_ratio_tendsto (show 2 ≤ r by omega)
    (exceptionalWindowLo_ratio_tendsto r)
  have hr0 : (r : ℝ) ≠ 0 := by exact_mod_cast (show r ≠ 0 by omega)
  have hval : (r : ℝ) * ((99 / 100 : ℝ) / r) = 99 / 100 := by field_simp <;> ring
  rw [hval] at h
  exact exp_div_nat_tendsto_zero_of_log_ratio (by norm_num) h

lemma exceptionalWindowLo_pair_correction_tendsto_zero {r : ℕ} (hr : 3 ≤ r) :
    Tendsto (fun n => 2 * isolationLowerExponent (Fin n) r (exceptionalWindowLo r n) -
      isolationPairExponent (Fin n) r (exceptionalWindowLo r n)) atTop (nhds 0) :=
  isolation_pair_correction_tendsto_zero (by omega) (exceptionalWindowLo_ratio_tendsto r)

lemma exceptionalWindowHi_exp_tendsto_zero {r : ℕ} (hr : 3 ≤ r) :
    Tendsto (fun n : ℕ => (n : ℝ) * Real.exp (-(((n-1).choose (r-1) : ℝ) *
      (exceptionalWindowHi r n : ℝ) / (n.choose r : ℝ)))) atTop (nhds 0) :=
  nat_mul_exp_neg_tendsto_zero_of_log_ratio (by norm_num)
    (exceptionalWindowHi_mean_ratio_tendsto (by omega : 1 ≤ r))
end LooseHamilton
