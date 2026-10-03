module

public import HittingTimeLooseHamilton.BiasedEntropyMean

public section

noncomputable section
namespace LooseHamilton.BiasedRoleInstance
variable {r : ℕ}

lemma privateFraction_pow_pos (hr : 3≤r) : 0<privateFraction r^(r-2) := by
  have hr' : (3:ℝ)≤r := by exact_mod_cast hr
  apply pow_pos
  unfold privateFraction
  exact div_pos (by linarith) (by linarith)

lemma cloneRelativeConstant_pos (hr : 3≤r) (C : ℝ) (hC : 0≤C) :
    0<cloneRelativeConstant r C := by
  apply div_pos _ (privateFraction_pow_pos hr)
  have hr' : (3:ℝ)≤r := by exact_mod_cast hr
  have hq : 0<(r:ℝ)-1 := by linarith
  unfold MixedCycleWitness.cloneMeanConstant
  positivity

lemma cloneLambda0_log (D : BiasedRoleInstance r) (hr : 3≤r) :
    Real.log D.cloneLambda0 = (r-2:ℕ)*Real.log (privateFraction r)+Real.log D.μ := by
  rw [cloneLambda0, Real.log_mul (ne_of_gt (privateFraction_pow_pos hr))
    (ne_of_gt (D.μ_pos hr)), Real.log_pow]

lemma cloneLambda0_le_mu (D : BiasedRoleInstance r) (hr : 3≤r) :
    D.cloneLambda0≤D.μ := by
  exact mul_le_of_le_one_left (le_of_lt (D.μ_pos hr)) (privateFraction_pow_bounds r hr).2
end LooseHamilton.BiasedRoleInstance
