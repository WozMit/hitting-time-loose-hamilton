module

public import HittingTimeLooseHamilton.CoreParameterBounds
public import HittingTimeLooseHamilton.FrameScales

public section

noncomputable section
namespace LooseHamilton
open Filter

theorem eventually_partition_window_enlargement (L L' : ℝ) (hL : 0<L) :
    ∀ᶠ n : ℕ in atTop, 1 ≤ L*(n:ℝ)^(1/10:ℝ) ∧
      L'*(n:ℝ)^(1/10:ℝ)+1 ≤ (n:ℝ)*(Real.log (n:ℝ))^(-1/8:ℝ) := by
  have hp : Tendsto (fun n : ℕ => (n:ℝ)^(1/10:ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0:ℝ)<1/10)).comp tendsto_natCast_atTop_atTop
  have hx : Tendsto (fun n : ℕ => (n:ℝ)^(1/10:ℝ)*Real.log n/n) atTop (nhds 0) := by
    have hh := tendsto_nat_rpow_mul_log_pow (by norm_num : (1/10:ℝ)-1<0) 1
    apply hh.congr'
    filter_upwards [eventually_ge_atTop (1:ℕ)] with n hn
    have hn0 : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
    rw [Real.rpow_sub hn0, Real.rpow_one, pow_one]
    ring
  have hy : Tendsto (fun n : ℕ => Real.log (n:ℝ)/(n:ℝ)) atTop (nhds 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp tendsto_natCast_atTop_atTop
  have hz : Tendsto (fun n : ℕ => (L'*(n:ℝ)^(1/10:ℝ)+1)*Real.log n/n) atTop (nhds 0) := by
    convert (hx.const_mul L').add hy using 1 <;> try simp
    ext n
    ring
  filter_upwards [(hp.const_mul_atTop hL).eventually (eventually_ge_atTop 1),
    hz.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1)),
    FrameScales.L1_tendsto.eventually (eventually_ge_atTop 1),
    eventually_ge_atTop (1:ℕ)] with n hp hz hlog hn
  have hn0 : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
  change 1≤Real.log (n:ℝ) at hlog
  have hlpos : 0<Real.log (n:ℝ) := by linarith
  refine ⟨hp,?_⟩
  have hh : L'*(n:ℝ)^(1/10:ℝ)+1 ≤ (n:ℝ)/Real.log n := by
    apply (le_div_iff₀ hlpos).mpr
    simpa only [one_mul] using ((div_lt_iff₀ hn0).mp hz).le
  apply hh.trans
  have hr : (Real.log (n:ℝ))^(-1:ℝ) ≤ (Real.log (n:ℝ))^(-1/8:ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hlog (by norm_num)
  rw [Real.rpow_neg_one] at hr
  simpa only [div_eq_mul_inv] using mul_le_mul_of_nonneg_left hr hn0.le
end LooseHamilton
