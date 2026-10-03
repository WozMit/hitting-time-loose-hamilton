module

public import HittingTimeLooseHamilton.PartitionUnionDecay
public import HittingTimeLooseHamilton.TerminalFeasibilityScales

public section

/-! The fixed-size partition Chernoff bound summed over all subsets and times. -/
noncomputable section
namespace LooseHamilton
open Filter Topology

lemma partition_concentration_prefactor_eventually {r : ℕ} (hr : 1≤r) :
    ∀ᶠ n : ℕ in atTop, ∀ M : ℕ,
      |(r:ℝ)*M/n-Real.log n|≤3*Real.log (Real.log n) →
      (2:ℝ)^n*((n.choose r:ℝ)+1)*2*
        Real.exp (-((Real.log n)^(-1/8:ℝ))^2*M/4+(n:ℝ)^(1/10:ℝ)) ≤
          4*partitionUnionError r (1/(8*(r:ℝ))) n := by
  have hr0 : (0:ℝ)<r := by exact_mod_cast (show 0<r by omega)
  filter_upwards [eventually_ge_atTop (1:ℕ),eventually_feasibility_parameters 0]
    with n hn hp
  intro M hM
  have hn0 : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
  have hn1 : (1:ℝ)≤n := by exact_mod_cast hn
  have hl : 0<Real.log (n:ℝ) := by linarith [hp.1]
  have hmean := hp.2.1 ((r:ℝ)*M/n) hM
  have hm : (n:ℝ)*Real.log n/(2*(r:ℝ))≤M := by
    have hm' := (le_div_iff₀ hn0).mp hmean
    apply (div_le_iff₀ (by positivity : (0:ℝ)<2*r)).mpr
    nlinarith [mul_nonneg hn0.le hl.le]
  have hpow : ((Real.log (n:ℝ))^(-1/8:ℝ))^2*Real.log n =
      (Real.log n)^(3/4:ℝ) := by
    calc
      _ = (Real.log n)^((-1/8:ℝ)*(2:ℕ))*(Real.log n)^(1:ℝ) := by rw [Real.rpow_mul_natCast hl.le,Real.rpow_one]
      _ = _ := by rw [←Real.rpow_add hl]; norm_num
  have hexp : Real.exp (-((Real.log n)^(-1/8:ℝ))^2*M/4+(n:ℝ)^(1/10:ℝ)) ≤
      Real.exp (-(1/(8*(r:ℝ)))*(n:ℝ)*(Real.log n)^(3/4:ℝ)+(n:ℝ)^(1/10:ℝ)) := by
    apply Real.exp_le_exp.mpr
    have hmul := mul_le_mul_of_nonneg_left hm (sq_nonneg ((Real.log n)^(-1/8:ℝ)))
    have hid : ((Real.log n)^(-1/8:ℝ))^2*((n:ℝ)*Real.log n/(2*(r:ℝ))) =
        (n:ℝ)*(Real.log n)^(3/4:ℝ)/(2*(r:ℝ)) := by rw [←hpow]; ring
    rw [hid] at hmul
    have hdiv := div_le_div_of_nonneg_right hmul (by norm_num : (0:ℝ)≤4)
    have heq : ((n:ℝ)*(Real.log n)^(3/4:ℝ)/(2*(r:ℝ)))/4 =
        (1/(8*(r:ℝ)))*(n:ℝ)*(Real.log n)^(3/4:ℝ) := by ring
    rw [heq] at hdiv
    linarith
  have hchoose : (n.choose r:ℝ)+1≤2*(n:ℝ)^r := by
    have hc : (n.choose r:ℝ)≤(n:ℝ)^r := by exact_mod_cast Nat.choose_le_pow n r
    have hpow1 : (1:ℝ)≤(n:ℝ)^r := one_le_pow₀ hn1
    linarith
  unfold partitionUnionError
  calc
    _ ≤ (2:ℝ)^n*(2*(n:ℝ)^r)*2*
        Real.exp (-(1/(8*(r:ℝ)))*(n:ℝ)*(Real.log n)^(3/4:ℝ)+(n:ℝ)^(1/10:ℝ)) := by
      gcongr
    _ = _ := by ring
end LooseHamilton
