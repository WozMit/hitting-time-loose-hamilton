module

public import HittingTimeLooseHamilton.EntropyPathRatesError

public section

noncomputable section
namespace LooseHamilton
open Filter

lemma tendsto_log_power_envelope (N : ℕ → ℕ)
    (hN : Tendsto N atTop atTop) (C a : ℝ) (ha : 0 < a) :
    Tendsto (fun n => C*(Real.log (N n:ℝ))^(-a)) atTop (nhds 0) := by
  have hn := (tendsto_natCast_atTop_atTop (R:=ℝ)).comp hN
  have hh := ((tendsto_rpow_neg_atTop ha).comp (Real.tendsto_log_atTop.comp hn)).const_mul C
  simpa only [mul_zero, Function.comp_def] using hh

lemma tendsto_zero_of_log_power_envelope (N : ℕ → ℕ)
    (hN : Tendsto N atTop atTop) (f : ℕ → ℝ) (C a : ℝ) (ha : 0 < a)
    (h0 : ∀ᶠ n in atTop, 0 ≤ f n)
    (hb : ∀ᶠ n in atTop, f n ≤ C*(Real.log (N n:ℝ))^(-a)) :
    Tendsto f atTop (nhds 0) :=
  squeeze_zero' h0 hb (tendsto_log_power_envelope N hN C a ha)

lemma tendsto_zero_of_sqrt_log_envelope (N : ℕ → ℕ)
    (hN : Tendsto N atTop atTop) (f : ℕ → ℝ) (B : ℝ)
    (h0 : ∀ᶠ n in atTop, 0 ≤ f n)
    (hb : ∀ᶠ n in atTop, f n ≤ B/Real.sqrt (Real.log (N n:ℝ))) :
    Tendsto f atTop (nhds 0) := by
  apply tendsto_zero_of_log_power_envelope N hN f B (1/2) (by norm_num) h0
  filter_upwards [hb] with n hn
  simpa only [div_sqrt_eq_log_power B _ (Real.log_natCast_nonneg _)] using hn

lemma tendsto_marker_ratio_of_power_envelope (N s : ℕ → ℕ)
    (hN : Tendsto N atTop atTop) (L : ℝ)
    (hb : ∀ᶠ n in atTop, (s n:ℝ) ≤ L*(N n:ℝ)^(1/10:ℝ)) :
    Tendsto (fun n => (s n:ℝ)/(N n:ℝ)) atTop (nhds 0) := by
  have hh := (tendsto_nat_rpow_ratio (by norm_num : (1/10:ℝ)<1)).const_mul L
  simp only [Real.rpow_one,mul_zero] at hh
  apply squeeze_zero' (Eventually.of_forall (fun n => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))) ?_ (hh.comp hN)
  filter_upwards [hb] with n hn
  simpa only [mul_div_assoc, Function.comp_def] using div_le_div_of_nonneg_right hn (Nat.cast_nonneg (N n))

end LooseHamilton
