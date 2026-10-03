module

public import HittingTimeLooseHamilton.BiasedEntropyRates
public import HittingTimeLooseHamilton.PathPerturbationScalars

public section

noncomputable section
namespace LooseHamilton
open Filter

/-- Every fixed negative logarithmic power is eventually below the reciprocal
of the iterated logarithm, including any fixed multiplicative constant. -/
theorem eventually_log_power_le_inv_loglog (K a : ℝ) (ha : 0 < a) :
    ∀ᶠ n : ℕ in atTop,
      K * (Real.log (n:ℝ))^(-a) ≤ 1 / Real.log (Real.log (n:ℝ)) := by
  have hlog := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  have ht := ((isLittleO_log_rpow_atTop ha).tendsto_div_nhds_zero.comp hlog).const_mul K
  simp only [mul_zero] at ht
  filter_upwards [hlog.eventually (eventually_gt_atTop 1),
    (tendsto_order.mp ht).2 1 (by norm_num)] with n hn ht
  change 1 < Real.log (n:ℝ) at hn
  have hl : 0 < Real.log (Real.log (n:ℝ)) := Real.log_pos hn
  apply (le_div_iff₀ hl).2
  have hpow : (Real.log (n:ℝ))^(-a) = ((Real.log (n:ℝ))^a)⁻¹ :=
    Real.rpow_neg (by linarith) a
  rw [hpow]
  simpa only [Function.comp_def, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using ht.le

/-- At the codegree scale, the reciprocal logarithm is at most eight times
its iterated-logarithm reference. -/
theorem eventually_inverse_log_codegree (C : ℝ) (hC : 0 < C) :
    ∀ᶠ n : ℕ in atTop, ∀ eta : ℝ, 0 < eta →
      eta ≤ C * (Real.log (n:ℝ))^(-1/4:ℝ) →
      0 < Real.log (1/eta) ∧
      1 / Real.log (1/eta) ≤ 8 / Real.log (Real.log (n:ℝ)) := by
  have hlog := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  have hbase : Tendsto (fun n : ℕ => (Real.log (n:ℝ))^(-1/4:ℝ)) atTop (nhds 0) := by
    simpa only [neg_div, Function.comp_def] using (tendsto_rpow_neg_atTop (by norm_num : (0:ℝ)<1/4)).comp hlog
  have hh := hbase.eventually (gt_mem_nhds (Real.exp_pos (-2*Real.log C)))
  filter_upwards [hlog.eventually (eventually_gt_atTop 1), hh] with n hn hs eta he hc
  change 1 < Real.log (n:ℝ) at hn
  have hl : 0 < Real.log (n:ℝ) := by linarith
  have hb : 0 < (Real.log (n:ℝ))^(-1/4:ℝ) := Real.rpow_pos_of_pos hl _
  have hb1 : (Real.log (n:ℝ))^(-1/4:ℝ) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg hn (by norm_num)
  have hsmall : 2*Real.log C ≤ Real.log (1 / (Real.log (n:ℝ))^(-1/4:ℝ)) := by
    have h := (Real.log_lt_iff_lt_exp hb).2 hs
    rw [one_div,Real.log_inv]
    linarith
  have h := FiniteEntropy.comparable_inverse_log_bound hb hb1 he hC hc hsmall
  refine ⟨h.1, h.2.trans_eq ?_⟩
  rw [one_div,Real.log_inv,Real.log_rpow hl]
  field_simp [ne_of_gt (Real.log_pos hn)] <;> ring

/-- The entropy square-root rate is a negative logarithmic half power. -/
lemma div_sqrt_eq_log_power (B x : ℝ) (hx : 0 ≤ x) :
    B / Real.sqrt x = B*x^(-(1/2):ℝ) := by
  rw [Real.sqrt_eq_rpow,Real.rpow_neg hx,div_eq_mul_inv]

/-- The usual logarithmic rounding cost is below the iterated-log scale. -/
theorem eventually_rounding_le_inv_loglog :
    ∀ᶠ n : ℕ in atTop,
      Real.log (n:ℝ)/(n:ℝ) ≤ 1/Real.log (Real.log (n:ℝ)) := by
  have hlog := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  have ht := tendsto_nat_rpow_mul_log_pow (by norm_num : (-1:ℝ)<0) 2
  filter_upwards [eventually_ge_atTop (2:ℕ),hlog.eventually (eventually_gt_atTop 1),
    (tendsto_order.mp ht).2 1 (by norm_num)] with n hn hl hh
  change 1 < Real.log (n:ℝ) at hl
  have hn0 : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
  have hl0 : 0 ≤ Real.log (n:ℝ) := by linarith
  have hll : 0 < Real.log (Real.log (n:ℝ)) := Real.log_pos hl
  have hllle : Real.log (Real.log (n:ℝ)) ≤ Real.log (n:ℝ) := by
    have h := Real.log_le_sub_one_of_pos (show 0<Real.log (n:ℝ) by linarith)
    linarith
  apply (le_div_iff₀ hll).2
  have hm := mul_le_mul_of_nonneg_left hllle (div_nonneg hl0 hn0.le)
  have he : Real.log (n:ℝ)/(n:ℝ)*Real.log (n:ℝ) =
      (n:ℝ)^(-1:ℝ)*(Real.log (n:ℝ))^2 := by rw [Real.rpow_neg_one]; ring
  exact hm.trans (by rw [he]; exact hh.le)

/-- A fixed logarithmic entropy loss can be absorbed into the square-root
logarithmic entropy tolerance. -/
theorem eventually_log_div_le_inv_sqrt_log (A : ℝ) :
    ∀ᶠ n : ℕ in atTop,
      A*Real.log (n:ℝ)/(n:ℝ) ≤ 1/Real.sqrt (Real.log (n:ℝ)) := by
  have ht := (tendsto_nat_power_log_real (by norm_num : (-1:ℝ)<0) (3/2)).const_mul A
  simp only [mul_zero] at ht
  filter_upwards [eventually_ge_atTop (2:ℕ),
    (tendsto_order.mp ht).2 1 (by norm_num)] with n hn hh
  have hn0 : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
  have hl : 0<Real.log (n:ℝ) := Real.log_pos (by exact_mod_cast (show 1<n by omega))
  apply (le_div_iff₀ (Real.sqrt_pos.2 hl)).2
  have he : Real.log (n:ℝ)*Real.sqrt (Real.log (n:ℝ)) =
      (Real.log (n:ℝ))^(3/2:ℝ) := by
    rw [Real.sqrt_eq_rpow]
    conv_lhs => lhs; rw [←Real.rpow_one (Real.log (n:ℝ))]
    rw [←Real.rpow_add hl]
    norm_num
  calc
    A*Real.log (n:ℝ)/(n:ℝ)*Real.sqrt (Real.log (n:ℝ)) =
      A*((n:ℝ)^(-1:ℝ)*(Real.log (n:ℝ))^(3/2:ℝ)) := by
        rw [Real.rpow_neg_one,←he]
        ring
    _ ≤ 1 := hh.le

end LooseHamilton
