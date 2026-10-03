module

public import HittingTimeLooseHamilton.ExceptionalSetAsymptotics

public section

noncomputable section
namespace LooseHamilton.CoreCountBenchmark
open Filter Topology

/-- Even the maximal allowed marker error is negligible on the N/log N scale. -/
theorem marker_error_ratio_tendsto_zero :
    Tendsto (fun N : ℕ => ((N:ℝ)^(1/10:ℝ)+1)*(Real.log N)^2/N)
      atTop (nhds 0) := by
  have h₁ : Tendsto (fun N : ℕ => (N:ℝ)^(1/10:ℝ)*(Real.log N)^2/N)
      atTop (nhds 0) := by
    have hh := tendsto_nat_rpow_mul_log_pow (by norm_num : (1/10:ℝ)-1<0) 2
    apply hh.congr'
    filter_upwards [eventually_ge_atTop (1:ℕ)] with N hN
    have hp : (0:ℝ)<N := by exact_mod_cast (show 0<N by omega)
    rw [Real.rpow_sub hp, Real.rpow_one]
    ring
  have h₂ : Tendsto (fun N : ℕ => (Real.log N)^2/(N:ℝ)) atTop (nhds 0) := by
    have hh := tendsto_nat_rpow_mul_log_pow (by norm_num : (-1:ℝ)<0) 2
    convert hh using 1
    ext N
    rw [Real.rpow_neg_one]
    ring
  convert h₁.add h₂ using 1 <;> try simp
  ext N
  ring

/-- Any fixed benchmark-error constant is absorbed uniformly over all admissible
marker counts, including their dependence on N. -/
theorem eventually_marker_error_le (C : ℝ) (hC : 0 ≤ C) :
    ∀ᶠ N : ℕ in atTop, ∀ s : ℕ, (s:ℝ) ≤ (N:ℝ)^(1/10:ℝ) →
      C*((s:ℝ)*Real.log N+Real.log N) ≤ (N:ℝ)/Real.log N := by
  have hh := marker_error_ratio_tendsto_zero.const_mul C
  simp only [mul_zero] at hh
  filter_upwards [eventually_ge_atTop (2:ℕ), hh.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1))]
    with N hN hb
  intro s hs
  have hN0 : (0:ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have hL : 0 < Real.log (N:ℝ) := Real.log_pos (by exact_mod_cast (show 1<N by omega))
  have hb' : C*((N:ℝ)^(1/10:ℝ)+1)*(Real.log N)^2 < (N:ℝ) := by
    have hquot : (C*((N:ℝ)^(1/10:ℝ)+1)*(Real.log N)^2)/(N:ℝ) < 1 := by
      convert hb using 1; ring
    simpa using (div_lt_iff₀ hN0).mp hquot
  apply (le_div_iff₀ hL).mpr
  have hm := mul_le_mul_of_nonneg_left hs (mul_nonneg hC (sq_nonneg (Real.log (N:ℝ))))
  nlinarith
end LooseHamilton.CoreCountBenchmark
