module

public import HittingTimeLooseHamilton.CandidateLogSurvival

public section

/-! A coarse positive survival factor sufficient for tiny completions. -/
noncomputable section
namespace LooseHamilton.CandidateLogSurvival

/-- The quarter constraints give a uniform lower survival factor. -/
theorem zeta_ge_exp_neg_two {m k τ : ℕ} (hm : 0<m)
    (hk4 : 4*k≤m) (ht4 : 4*τ≤m) {ν : ℝ} (hν : (τ:ℝ)*k/m≤ν) :
    Real.exp (-2*ν) ≤ zeta m k τ := by
  have hs : k+τ<m := by omega
  have hz := zeta_pos hs
  have hl := (log_zeta_bounds hm hs).1
  have hmR : (0:ℝ)<m := by exact_mod_cast hm
  have hdR : (0:ℝ)<(m-k-τ:ℕ) := by exact_mod_cast (show 0<m-k-τ by omega)
  have hhalf : (m:ℝ)≤2*(m-k-τ:ℕ) := by
    exact_mod_cast (show m≤2*(m-k-τ) by omega)
  have hfrac : (k:ℝ)*τ/(m-k-τ:ℕ) ≤ 2*((τ:ℝ)*k/m) := by
    apply (div_le_iff₀ hdR).mpr
    apply (mul_le_mul_iff_left₀ hmR).mp
    field_simp
    nlinarith [mul_le_mul_of_nonneg_left hhalf (show 0≤(k:ℝ)*τ by positivity)]
  have hlog : -2*ν ≤ Real.log (zeta m k τ) := by linarith
  simpa only [Real.exp_log hz] using Real.exp_le_exp.mpr hlog

end LooseHamilton.CandidateLogSurvival
