module

public import HittingTimeLooseHamilton.FrameConcentrationScales
public import HittingTimeLooseHamilton.CandidateLogSurvivalBudget

public section

noncomputable section
namespace LooseHamilton.FrameScales
open Filter Topology

/-- The entire logarithmic survival loss fits in one unit of original-size
entropy error, uniformly before any frame is selected. -/
theorem eventually_restricted_budget_error :
    ∀ᶠ N : ℕ in atTop,
      0≤alpha N/100000 ∧ alpha N/100000≤1/2 ∧
      2*nu N+2*(alpha N/100000)≤(N:ℝ)/Real.sqrt (L1 N) := by
  have ht := (isLittleO_log_rpow_rpow_atTop (2:ℝ)
    (by norm_num : (0:ℝ)<1)).tendsto_div_nhds_zero.comp tendsto_natCast_atTop_atTop
  simp only [Real.rpow_two,Real.rpow_one] at ht
  filter_upwards [eventual_range,L1_tendsto.eventually (eventually_ge_atTop 1),
    ht.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1/3)),
    eventually_gt_atTop 0] with N hR h1 hsmall hN
  have hNpos : (0:ℝ)<N := by exact_mod_cast hN
  have h21 : L2 N≤L1 N := by
    have := Real.log_le_sub_one_of_pos hR.1
    change Real.log (L1 N)≤L1 N
    linarith
  have h32 : L3 N≤L2 N := by
    have := Real.log_le_sub_one_of_pos hR.2.1
    change Real.log (L2 N)≤L2 N
    linarith
  have hnu : nu N≤L1 N := by dsimp [nu]; linarith [hR.2.2.1]
  have hs : Real.sqrt (L1 N)≤L1 N := Real.sqrt_le_iff.mpr ⟨hR.1.le,by nlinarith⟩
  have hh0 : 0≤alpha N/100000 := by exact div_nonneg hR.2.2.2.1.le (by norm_num)
  have hh1 : alpha N/100000≤1/2 := by linarith [hR.2.2.2.2.1]
  refine ⟨hh0,hh1,?_⟩
  apply (le_div_iff₀ (Real.sqrt_pos.mpr hR.1)).mpr
  have hprod := mul_le_mul_of_nonneg_left hs
    (show 0≤2*nu N+2*(alpha N/100000) by have := hR.2.2.2.2.2.1; positivity)
  have hsq : 3*(L1 N)^2≤(N:ℝ) := by
    have hh := (div_lt_iff₀ hNpos).mp hsmall
    change (L1 N)^2 < (1/3:ℝ)*N at hh
    linarith
  nlinarith
end LooseHamilton.FrameScales
namespace LooseHamilton.CandidateLogSurvival

/-- The restricted hypergeometric center loses at most twice the batch scale. -/
lemma log_zeta_lower_of_quarters {m k τ : ℕ} {ν : ℝ}
    (hm : 0 < m) (hk : 4*k≤m) (ht : 4*τ≤m)
    (hν : (τ:ℝ)*k/m≤ν) : -2*ν≤Real.log (zeta m k τ) := by
  have hs : k+τ<m := by omega
  have hl := (log_zeta_bounds hm hs).1
  have hmR : (0:ℝ)<m := by exact_mod_cast hm
  have hdR : (0:ℝ)<(m-k-τ:ℕ) := by exact_mod_cast (show 0<m-k-τ by omega)
  have hd : (m:ℝ)≤2*(m-k-τ:ℕ) := by exact_mod_cast (show m≤2*(m-k-τ) by omega)
  have hh : (k:ℝ)*τ/(m-k-τ:ℕ)≤2*((τ:ℝ)*k/m) := by
    rw [← mul_div_assoc]
    apply (div_le_div_iff₀ hdR hmR).mpr
    nlinarith [mul_le_mul_of_nonneg_left hd (show 0≤(k:ℝ)*τ by positivity)]
  linarith
end LooseHamilton.CandidateLogSurvival
