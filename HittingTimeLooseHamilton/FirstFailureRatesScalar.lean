module

public import HittingTimeLooseHamilton.FirstFailureRatesVariance
public import Mathlib.Analysis.SpecialFunctions.Sqrt

public section

noncomputable section
namespace LooseHamilton.FirstFailureRates
open Filter Topology

/-- Terminal conditioning has subdominant exponential cost on the N/log N scale. -/
theorem feasibility_cost_ratio_tendsto_zero :
    Tendsto (fun N : ℕ => (N:ℝ)^(1/10:ℝ)*Real.log N/N) atTop (nhds 0) := by
  have hh := tendsto_nat_rpow_mul_log_pow (by norm_num : (1/10:ℝ)-1<0) 1
  apply hh.congr'
  filter_upwards [eventually_ge_atTop (1:ℕ)] with N hN
  have hp : (0:ℝ)<N := by exact_mod_cast (show 0<N by omega)
  rw [Real.rpow_sub hp, Real.rpow_one, pow_one]
  ring

/-- The inflated positive variance budget, bootstrap threshold, and conditioned
exponential tail all hold uniformly in the terminal conditioning probability. -/
theorem eventually_scalar_rates (C : ℝ) (hC : 0 < C) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop,
      0 < (N:ℝ) ∧ 0 < Real.log (N:ℝ) ∧
      0 < (N:ℝ)/Real.log N ∧ 0 < C*((N:ℝ)/Real.log N) ∧
      (1+C)*((N:ℝ)/Real.log N) < (N:ℝ)/Real.sqrt (Real.log N) ∧
      ∀ β : ℝ, Real.exp (-(N:ℝ)^(1/10:ℝ)) ≤ β →
        β⁻¹ * Real.exp (-((N:ℝ)/Real.log N)^2 /
          (2*(C*((N:ℝ)/Real.log N)))) ≤ ε := by
  have hlog : Tendsto (fun N : ℕ => Real.log (N:ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hpow : Tendsto (fun N : ℕ => (N:ℝ)^(1/10:ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0:ℝ)<1/10)).comp tendsto_natCast_atTop_atTop
  have hexp := Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp hpow)
  filter_upwards [eventually_ge_atTop (1:ℕ),
    hlog.eventually (eventually_gt_atTop ((1+C)^2)),
    feasibility_cost_ratio_tendsto_zero.eventually
      (gt_mem_nhds (by positivity : (0:ℝ)<1/(4*C))),
    hexp.eventually (gt_mem_nhds hε)] with N hN hLlarge hratio hexp
  have hN0 : (0:ℝ)<N := by exact_mod_cast hN
  have hL : 0 < Real.log (N:ℝ) := lt_of_le_of_lt (sq_nonneg _) hLlarge
  have ha : 0 < (N:ℝ)/Real.log N := div_pos hN0 hL
  have hW : 0 < C*((N:ℝ)/Real.log N) := mul_pos hC ha
  have hsqrt : 0 < Real.sqrt (Real.log (N:ℝ)) := Real.sqrt_pos.mpr hL
  have hs : 1+C < Real.sqrt (Real.log (N:ℝ)) := by
    nlinarith [Real.sq_sqrt hL.le]
  refine ⟨hN0,hL,ha,hW,?_,?_⟩
  · apply (lt_div_iff₀ hsqrt).mpr
    apply (mul_lt_mul_iff_left₀ hL).mp
    have he : ((1+C)*((N:ℝ)/Real.log N)*Real.sqrt (Real.log N))*Real.log N =
        (1+C)*(N:ℝ)*Real.sqrt (Real.log N) := by field_simp
    rw [he]
    have hh := mul_lt_mul_of_pos_right hs hsqrt
    rw [Real.mul_self_sqrt hL.le] at hh
    nlinarith
  · intro β hβ
    have hp : 0 < Real.exp (-(N:ℝ)^(1/10:ℝ)) := Real.exp_pos _
    have hβ0 : 0 < β := hp.trans_le hβ
    have hib : β⁻¹ ≤ Real.exp ((N:ℝ)^(1/10:ℝ)) := by
      have hh := (one_div_le_one_div_of_le hp hβ)
      simpa only [one_div, Real.exp_neg, inv_inv] using hh
    have hrat := (div_lt_iff₀ hN0).mp hratio
    have hpowbound : (N:ℝ)^(1/10:ℝ) ≤ ((N:ℝ)/Real.log N)/(4*C) := by
      apply (le_div_iff₀ (by positivity : 0<4*C)).mpr
      apply (le_div_iff₀ hL).mpr
      have hh := (lt_div_iff₀ (by positivity : 0<4*C)).mp
        (show (N:ℝ)^(1/10:ℝ)*Real.log N < (N:ℝ)/(4*C) by convert hrat using 1; ring)
      nlinarith
    have he : -((N:ℝ)/Real.log N)^2 / (2*(C*((N:ℝ)/Real.log N))) =
        -((N:ℝ)/Real.log N)/(2*C) := by field_simp <;> ring
    calc
      _ ≤ Real.exp ((N:ℝ)^(1/10:ℝ)) *
          Real.exp (-((N:ℝ)/Real.log N)^2 / (2*(C*((N:ℝ)/Real.log N)))) :=
        mul_le_mul_of_nonneg_right hib (Real.exp_pos _).le
      _ = Real.exp ((N:ℝ)^(1/10:ℝ)-((N:ℝ)/Real.log N)/(2*C)) := by
        rw [he, ← Real.exp_add]; congr 1; ring
      _ ≤ Real.exp (-(N:ℝ)^(1/10:ℝ)) := by
        apply Real.exp_le_exp.mpr
        have hh : ((N:ℝ)/Real.log N)/(2*C) = 2*(((N:ℝ)/Real.log N)/(4*C)) := by ring
        rw [hh]; linarith
      _ ≤ ε := hexp.le
end LooseHamilton.FirstFailureRates
