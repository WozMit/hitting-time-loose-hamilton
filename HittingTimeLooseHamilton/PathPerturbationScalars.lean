module

public import HittingTimeLooseHamilton.CoreParameterBounds
public import HittingTimeLooseHamilton.PathRegularityModels

public section
noncomputable section
namespace LooseHamilton
open Filter

/-- Losing at most half the edge mass and at most half the vertices changes
the actual mean degree by factors between one half and two. -/
theorem mean_degree_perturbation {n n' m m' r b : ℝ}
    (hn : 0 < n) (hn' : n/2 ≤ n') (hnn : n' ≤ n)
    (hm : 0 ≤ m) (hmm : m' ≤ m) (hr : 0 ≤ r)
    (hloss : m-m' ≤ b*(r*m/n)) (hbudget : b*r ≤ n/2) :
    (r*m/n)/2 ≤ r*m'/n' ∧ r*m'/n' ≤ 2*(r*m/n) := by
  have hn'0 : 0 < n' := by linarith
  have hmhalf : m/2 ≤ m' := by
    have ht := mul_le_mul_of_nonneg_right hbudget hm
    have hid : b*(r*m/n) = (b*r*m)/n := by ring
    rw [hid] at hloss
    have hl := (le_div_iff₀ hn).mp hloss
    nlinarith
  have hm' : 0 ≤ m' := by linarith
  constructor
  · apply (le_div_iff₀ hn'0).mpr
    have ha : ((r*m/n)/2)*n' ≤ ((r*m/n)/2)*n :=
      mul_le_mul_of_nonneg_left hnn (by positivity)
    have hb : ((r*m/n)/2)*n = r*(m/2) := by field_simp <;> ring
    rw [hb] at ha
    exact ha.trans (mul_le_mul_of_nonneg_left hmhalf hr)
  · apply (div_le_iff₀ hn'0).mpr
    have ha : (r*m/n)*n ≤ (r*m/n)*(2*n') :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    have hb : (r*m/n)*n = r*m := by field_simp
    rw [hb] at ha
    nlinarith [mul_le_mul_of_nonneg_left hmm hr]

/-- Negative logarithmic powers grow under vertex deletion. -/
theorem log_rpow_deletion_mono {n n' a : ℝ} (hn' : 1 < n')
    (hnn : n' ≤ n) (ha : a ≤ 0) :
    (Real.log n)^a ≤ (Real.log n')^a := by
  exact Real.rpow_le_rpow_of_nonpos (Real.log_pos hn')
    (Real.log_le_log (by linarith) hnn) ha

/-- Balanced-set windows survive a bounded change of the ambient vertex count. -/
theorem balanced_window_deletion {n n' a z L x : ℝ}
    (hn' : 0 ≤ n') (hnn : n' ≤ n) (ha : 0 ≤ a) (hL : 0 ≤ L)
    (hz : n-n' = z) (hsmall : a*z ≤ n^(1/10:ℝ))
    (hA : |x-a*n'| ≤ L*n'^(1/10:ℝ)) :
    |x-a*n| ≤ (L+1)*n^(1/10:ℝ) := by
  have hpow : n'^(1/10:ℝ) ≤ n^(1/10:ℝ) :=
    Real.rpow_le_rpow hn' hnn (by norm_num)
  have he : |a*n'-a*n| = a*z := by
    rw [show a*n'-a*n = -(a*z) by rw [← hz]; ring,abs_neg,abs_of_nonneg]
    exact mul_nonneg ha (by rw [← hz]; linarith)
  have ht := abs_add_le (x-a*n') (a*n'-a*n)
  rw [show x-a*n'+(a*n'-a*n)=x-a*n by ring,he] at ht
  nlinarith [mul_le_mul_of_nonneg_left hpow hL]

/-- Any fixed multiple of n^(1/10), together with a fixed error, is eventually
smaller than half of n. -/
theorem eventually_sublinear_budget (a b : ℝ) :
    ∀ᶠ n : ℕ in atTop, 1 ≤ n ∧ a+b*(n:ℝ)^(1/10:ℝ) ≤ (n:ℝ)/2 := by
  have hc : Tendsto (fun n : ℕ => a/(n:ℝ)) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hp := tendsto_nat_rpow_ratio (by norm_num : (1/10:ℝ)<1)
  simp only [Real.rpow_one] at hp
  have hs := hc.add (hp.const_mul b)
  simp only [mul_zero,add_zero] at hs
  filter_upwards [eventually_ge_atTop (1:ℕ),
    (tendsto_order.mp hs).2 (1/2) (by norm_num)] with n hn h
  refine ⟨hn,?_⟩
  have hn0 : (0:ℝ)<n := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have he : a/(n:ℝ)+b*((n:ℝ)^(1/10:ℝ)/(n:ℝ)) =
      (a+b*(n:ℝ)^(1/10:ℝ))/(n:ℝ) := by ring
  rw [he] at h
  linarith [(div_lt_iff₀ hn0).mp h]

/-- Fixed losses in degree are negligible at the codegree error scale. -/
theorem eventually_log_error_small (a : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, a*(Real.log (n:ℝ))^(-1/4:ℝ) ≤ ε := by
  have hlog := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  have hp := (tendsto_rpow_neg_atTop (by norm_num : (0:ℝ)<1/4)).comp hlog
  have ht := hp.const_mul a
  simp only [mul_zero] at ht
  filter_upwards [(tendsto_order.mp ht).2 ε hε] with n h
  simpa only [Function.comp_apply,neg_div] using h.le

lemma tendsto_nat_power_log_real {a : ℝ} (ha : a < 0) (t : ℝ) :
    Tendsto (fun n : ℕ => (n:ℝ)^a*(Real.log (n:ℝ))^t) atTop (nhds 0) := by
  have hh := ((isLittleO_log_rpow_rpow_atTop t (s := -a) (neg_pos.mpr ha)).tendsto_div_nhds_zero).comp
    (tendsto_natCast_atTop_atTop (R:=ℝ))
  convert hh using 1
  ext n
  change (n:ℝ)^a*(Real.log (n:ℝ))^t = (Real.log (n:ℝ))^t/(n:ℝ)^(-a)
  rw [Real.rpow_neg (Nat.cast_nonneg n),div_inv_eq_mul,mul_comm]

/-- Bounded and sublinear edge losses fit into the partition tolerance. -/
theorem eventually_partition_loss_budget (a b : ℝ) :
    ∀ᶠ n : ℕ in atTop, a+b*(n:ℝ)^(1/10:ℝ) ≤
      (n:ℝ)*(Real.log (n:ℝ))^(-1/8:ℝ) := by
  have h₁ := (tendsto_nat_power_log_real (by norm_num : (-1:ℝ)<0) (1/8)).const_mul a
  have h₂ := (tendsto_nat_power_log_real (by norm_num : (-9/10:ℝ)<0) (1/8)).const_mul b
  have hs := h₁.add h₂
  simp only [mul_zero,add_zero] at hs
  filter_upwards [eventually_ge_atTop (2:ℕ),
    (tendsto_order.mp hs).2 1 (by norm_num)] with n hn hh
  have hn0 : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
  have hl : 0 < Real.log (n:ℝ) := Real.log_pos (by exact_mod_cast (show 1<n by omega))
  have he : a*((n:ℝ)^(-1:ℝ)*(Real.log (n:ℝ))^(1/8:ℝ))+
      b*((n:ℝ)^(-9/10:ℝ)*(Real.log (n:ℝ))^(1/8:ℝ)) =
      (a+b*(n:ℝ)^(1/10:ℝ))*((Real.log (n:ℝ))^(1/8:ℝ))/(n:ℝ) := by
    have hp : (n:ℝ)^(-9/10:ℝ) = (n:ℝ)^(1/10:ℝ)/(n:ℝ) := by
      calc
        _ = (n:ℝ)^((1/10:ℝ)-1) := by norm_num
        _ = (n:ℝ)^(1/10:ℝ)/(n:ℝ)^(1:ℝ) := Real.rpow_sub hn0 _ _
        _ = _ := by rw [Real.rpow_one]
    rw [hp,Real.rpow_neg_one]
    ring
  rw [he] at hh
  have hi := (div_lt_iff₀ hn0).mp hh
  have hp : 0 < (Real.log (n:ℝ))^(1/8:ℝ) := Real.rpow_pos_of_pos hl _
  have hb := (le_div_iff₀ hp).mpr hi.le
  rw [show (-1/8:ℝ) = -(1/8:ℝ) by ring,Real.rpow_neg hl.le]
  simpa only [one_mul,div_eq_mul_inv] using hb
end LooseHamilton
