module

public import HittingTimeLooseHamilton.FrameScales
public import HittingTimeLooseHamilton.EntropyPathRates
public import HittingTimeLooseHamilton.ForwardReverseAsymptotic

public section

noncomputable section
namespace LooseHamilton.FrameScales
open Filter Topology

lemma exp_four_nu (N : ℕ) (h : 0 < L2 N) :
    Real.exp (4 * nu N) = (L2 N)^(1/25:ℝ) := by
  rw [Real.rpow_def_of_pos h]
  congr 1
  dsimp [nu,L3]
  ring

/-- Every fixed power of the third logarithm is negligible against a positive
power of the second logarithm. -/
lemma third_power_div_second_power (a b : ℝ) (hb : 0 < b) :
    Tendsto (fun N => (L3 N)^a / (L2 N)^b) atTop (nhds 0) := by
  exact ((isLittleO_log_rpow_rpow_atTop a hb).tendsto_div_nhds_zero).comp L2_tendsto

lemma alpha_power (N : ℕ) (h : 0 < L3 N) (a : ℝ) :
    (alpha N)^a = (L3 N)^(-a/100) := by
  rw [alpha,←Real.rpow_mul h.le]
  congr 1
  ring

/-- The static exceptional fraction is little-o of every fixed power of alpha. -/
lemma static_error_div_alpha_power (a : ℝ) :
    Tendsto (fun N => (1 / (alpha N * Real.sqrt (L2 N))) / (alpha N)^a)
      atTop (nhds 0) := by
  apply (third_power_div_second_power ((a+1)/100) (1/2) (by norm_num)).congr'
  filter_upwards [eventual_range] with N hN
  have h3 : 0 < L3 N := by linarith [hN.2.2.1]
  have ha := hN.2.2.2.1
  symm
  rw [Real.sqrt_eq_rpow,alpha_power N h3]
  dsimp [alpha]
  have hr : (L3 N)^(-1/100:ℝ) * (L3 N)^(-a/100) =
      ((L3 N)^((a+1)/100))⁻¹ := by
    rw [←Real.rpow_add h3,←Real.rpow_neg h3.le]
    congr 1
    ring
  calc
    _ = 1 / (((L3 N)^(-1/100:ℝ) * (L3 N)^(-a/100)) * (L2 N)^(1/2:ℝ)) := by ring
    _ = _ := by rw [hr]; field_simp

/-- Chebyshev's probability scale divided by any fixed power of alpha vanishes. -/
lemma failure_scale_div_alpha_power (a : ℝ) :
    Tendsto (fun N => ((alpha N/100000)^(-2:ℝ) * (L2 N)^(-24/25:ℝ)) /
      (alpha N)^a) atTop (nhds 0) := by
  have hh := (third_power_div_second_power ((a+2)/100) (24/25) (by norm_num)).const_mul
    (100000^2:ℝ)
  simp only [mul_zero] at hh
  apply hh.congr'
  filter_upwards [eventual_range] with N hN
  have h3 : 0 < L3 N := by linarith [hN.2.2.1]
  have ha := hN.2.2.2.1
  symm
  rw [Real.div_rpow ha.le (by norm_num)]
  have hr : (alpha N)^(-2:ℝ) / (alpha N)^a = (L3 N)^((a+2)/100) := by
    rw [alpha_power N h3 (-2),alpha_power N h3 a,←Real.rpow_sub h3]
    congr 1
    ring
  have hc : (100000:ℝ)^(-2:ℝ) = (100000^2:ℝ)⁻¹ := by
    rw [Real.rpow_neg (by norm_num : (0:ℝ)≤100000),Real.rpow_two]
  rw [hc]
  have hp : (L2 N)^(-24/25:ℝ) = ((L2 N)^(24/25:ℝ))⁻¹ := by
    rw [←Real.rpow_neg hN.2.1.le]
    congr 1
    ring
  rw [hp]
  calc
    _ = (100000^2:ℝ) * ((alpha N)^(-2:ℝ) / (alpha N)^a) / (L2 N)^(24/25:ℝ) := by
      simp only [div_eq_mul_inv,inv_inv]; ring
    _ = _ := by rw [hr]; ring

lemma alpha_mul_nu (N : ℕ) (h : 0 < L3 N) :
    alpha N * nu N = (L3 N)^(99/100:ℝ) / 100 := by
  dsimp [alpha,nu]
  rw [←mul_div_assoc]
  congr 1
  conv_lhs => rhs; rw [←Real.rpow_one (L3 N)]
  rw [←Real.rpow_add h]
  norm_num

lemma target_exponent_tendsto :
    Tendsto (fun N => L1 N * (L3 N)^(99/100:ℝ)) atTop atTop := by
  exact Filter.Tendsto.atTop_mul_atTop₀ L1_tendsto
    ((tendsto_rpow_atTop (by norm_num : (0:ℝ)<99/100)).comp L3_tendsto)

end LooseHamilton.FrameScales
