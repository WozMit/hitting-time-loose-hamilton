module

public import HittingTimeLooseHamilton.TerminalFeasibilityScales
public import HittingTimeLooseHamilton.NormalizationAsymptotic

public section

/-! Scalar estimates for the terminal low-degree set. -/
noncomputable section
namespace LooseHamilton
open Filter Topology

@[expose] def terminalLowSetSize (n : ℕ) : ℕ := Nat.ceil ((n:ℝ)^(1/4:ℝ))

lemma terminalLowSetSize_ratio :
    Tendsto (fun n => (terminalLowSetSize n:ℝ)/(n:ℝ)) atTop (𝓝 0) := by
  have ht : Tendsto (fun n : ℕ => (n:ℝ)^(1/4:ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0:ℝ)<1/4)).comp tendsto_natCast_atTop_atTop
  have h := (tendsto_nat_ceil_div_atTop.comp ht).mul
    (tendsto_nat_rpow_ratio (by norm_num : (1/4:ℝ)<1))
  simp only [mul_zero, Real.rpow_one] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop (1:ℕ)] with n hn
  have hp : (n:ℝ)^(1/4:ℝ) ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos (by exact_mod_cast (show 0<n by omega)) _)
  exact div_mul_div_cancel₀ hp

lemma terminalLowSet_complement_ratio :
    Tendsto (fun n => ((n-terminalLowSetSize n:ℕ):ℝ)/(n:ℝ)) atTop (𝓝 1) := by
  have hid : Tendsto (fun n : ℕ => (n:ℝ)/(n:ℝ)) atTop (𝓝 1) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop (1:ℕ)] with n hn
    simp [show (n:ℝ) ≠ 0 by exact_mod_cast (show n≠0 by omega)]
  simpa using normalized_nat_sub_tendsto tendsto_id hid terminalLowSetSize_ratio (by norm_num : (0:ℝ)<1)

lemma terminalLowSet_complement_atTop : Tendsto (fun n => n-terminalLowSetSize n) atTop atTop :=
  tendsto_nat_atTop_of_ratio tendsto_id terminalLowSet_complement_ratio (by norm_num)

lemma terminalLowSet_star_ratio (r : ℕ) :
    Tendsto (fun n => ((n-terminalLowSetSize n).choose (r-1):ℝ)/
      ((n-1).choose (r-1):ℝ)) atTop (𝓝 1) := by
  have h1 := normalized_choose_tendsto terminalLowSet_complement_atTop tendsto_id
    terminalLowSet_complement_ratio (r-1)
  have hid : Tendsto (fun n : ℕ => (n:ℝ)/(n:ℝ)) atTop (𝓝 1) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop (1:ℕ)] with n hn
    simp [show (n:ℝ) ≠ 0 by exact_mod_cast (show n≠0 by omega)]
  have hsub := normalized_nat_sub_const_tendsto tendsto_id tendsto_id hid 1
  have hsubtop := tendsto_nat_atTop_of_ratio tendsto_id hsub (by norm_num : (0:ℝ)<1)
  have hden := normalized_choose_tendsto hsubtop tendsto_id hsub (r-1)
  have h := h1.div hden (by positivity)
  simp only [one_pow, div_self (by positivity : (1:ℝ)/(r-1).factorial ≠ 0)] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop (1:ℕ)] with n hn
  have hp : (n:ℝ)^(r-1) ≠ 0 := pow_ne_zero _ (by exact_mod_cast (show n≠0 by omega))
  exact div_div_div_cancel_right₀ hp _ _

lemma terminalLowSet_mean_eventually {r : ℕ} (hr : 1 ≤ r) :
    ∀ᶠ n : ℕ in atTop, ∀ M : ℕ,
      |(r:ℝ)*M/n-Real.log n| ≤ 3*Real.log (Real.log n) →
      (98/100:ℝ)*Real.log n ≤
        ((99/100:ℝ)*M/(n.choose r:ℝ))*((n-terminalLowSetSize n).choose (r-1):ℝ) := by
  have hlog : Tendsto (fun n : ℕ => Real.log (n:ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hratio := Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp hlog
  filter_upwards [eventually_ge_atTop r, hlog.eventually (eventually_ge_atTop 1),
    (terminalLowSet_star_ratio r).eventually_const_lt (by norm_num : (999/1000:ℝ)<1),
    (tendsto_order.mp hratio).2 (1/3000) (by norm_num)] with n hrn hl hs hh
  intro M hM
  have hn : 0<n := by omega
  have hn0 : (0:ℝ)<n := by exact_mod_cast hn
  have hk : (0:ℝ)<n.choose r := by exact_mod_cast Nat.choose_pos hrn
  have hd : (0:ℝ)<(n-1).choose (r-1) := by exact_mod_cast Nat.choose_pos (show r-1≤n-1 by omega)
  have hm : (999/1000:ℝ)*Real.log n ≤ (r:ℝ)*M/n := by
    have hh' := (div_lt_iff₀ (show 0<Real.log (n:ℝ) by linarith)).mp hh
    have hm' := (abs_le.mp hM).1
    linarith
  have hstar := (lt_div_iff₀ hd).mp hs
  have he : (((99/100:ℝ)*M/(n.choose r:ℝ))*((n-terminalLowSetSize n).choose (r-1):ℝ)) =
      (99/100:ℝ)*((r:ℝ)*M/n)*
        (((n-terminalLowSetSize n).choose (r-1):ℝ)/((n-1).choose (r-1):ℝ)) := by
    have hi := vertex_incidence_ratio hr hrn
    calc
      _ = (99/100:ℝ)*M*((((n-1).choose (r-1):ℝ)/(n.choose r:ℝ)))*
        (((n-terminalLowSetSize n).choose (r-1):ℝ)/((n-1).choose (r-1):ℝ)) := by field_simp <;> ring
      _ = _ := by rw [hi]; ring
  rw [he]
  have hmul := mul_le_mul hm hs.le (by norm_num : (0:ℝ)≤999/1000)
    (by positivity : 0≤(r:ℝ)*M/n)
  nlinarith
end LooseHamilton
