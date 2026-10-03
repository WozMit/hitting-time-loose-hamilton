module

public import HittingTimeLooseHamilton.EntropyPathRates
public import HittingTimeLooseHamilton.BiasedRoleModels

public section

noncomputable section
namespace LooseHamilton
open Filter

/-- All six printed errors in Theorem 6.1 fit into the iterated-logarithm
budget under the degree, partition, marker and entropy rates in the consequences of Section 6.
The constant is uniform; the threshold may depend on all fixed parameters. -/
theorem eventually_biasedRoleError_le_inv_loglog
    (r : ℕ) (hr : 3 ≤ r) (C B L : ℝ) (hC : 0 < C) :
    ∀ᶠ N : ℕ in atTop, ∀ (s : ℕ) (ξ δ η : ℝ),
      (s:ℝ) ≤ L*(N:ℝ)^(1/10:ℝ) →
      ξ ≤ B / Real.sqrt (Real.log (N:ℝ)) →
      δ ≤ C*(Real.log (N:ℝ))^(-1/8:ℝ) →
      0 < η → η ≤ C*(Real.log (N:ℝ))^(-1/4:ℝ) →
      biasedRoleError r N s ξ δ η ≤ 13/Real.log (Real.log (N:ℝ)) := by
  let a : ℝ := 1/(2*((r:ℝ)-1))
  have hrR : (3:ℝ) ≤ r := by exact_mod_cast hr
  have ha : 0 < a := one_div_pos.mpr (by linarith)
  have hlog := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  filter_upwards [eventually_ge_atTop (2:ℕ),hlog.eventually (eventually_gt_atTop 1),
    eventually_log_power_le_inv_loglog B (1/2) (by norm_num),
    eventually_log_power_le_inv_loglog C (1/8) (by norm_num),
    eventually_log_power_le_inv_loglog 1 (1/8) (by norm_num),
    eventually_log_power_le_inv_loglog (C^a) (a/4) (by positivity),
    eventually_partition_loss_budget 0 L,
    eventually_inverse_log_codegree C hC,
    eventually_rounding_le_inv_loglog] with N hN hlogN hx hd hm hp hs hi hn
  intro s ξ δ η hsm hξ hδ hη hηb
  change 1 < Real.log (N:ℝ) at hlogN
  have hN0 : (0:ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have hl : 0 < Real.log (N:ℝ) := by linarith
  have hx' : ξ ≤ 1/Real.log (Real.log (N:ℝ)) := by
    apply hξ.trans
    rw [div_sqrt_eq_log_power B _ hl.le]
    exact hx
  have hd' : δ ≤ 1/Real.log (Real.log (N:ℝ)) := hδ.trans (by simpa only [neg_div] using hd)
  have hm' : (s:ℝ)/(N:ℝ) ≤ 1/Real.log (Real.log (N:ℝ)) := by
    have hh : (s:ℝ)/(N:ℝ) ≤ (Real.log (N:ℝ))^(-1/8:ℝ) := by
      apply (div_le_iff₀ hN0).2
      nlinarith [hs]
    exact hh.trans (by simpa only [one_mul,neg_div] using hm)
  have hp' : η^a ≤ 1/Real.log (Real.log (N:ℝ)) := by
    have hh' := Real.rpow_le_rpow hη.le hηb ha.le
    rw [Real.mul_rpow hC.le (Real.rpow_nonneg hl.le _),←Real.rpow_mul hl.le] at hh'
    have he : (-1/4:ℝ)*a = -(a/4) := by ring
    rw [he] at hh'
    exact hh'.trans hp
  have hi' := (hi η hη hηb).2
  unfold biasedRoleError
  change ξ+δ+(s:ℝ)/(N:ℝ)+η^a+1/Real.log (1/η)+Real.log (N:ℝ)/(N:ℝ) ≤ _
  simp only [div_eq_mul_inv] at hx' hd' hm' hp' hi' hn ⊢
  linarith

end LooseHamilton
