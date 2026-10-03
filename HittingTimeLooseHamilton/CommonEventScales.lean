module

public import HittingTimeLooseHamilton.CandidateBalanceSpecification
public import HittingTimeLooseHamilton.FrameScales

public section

/-! Superpolynomial error scales for the finite common event. -/
noncomputable section
namespace LooseHamilton.FrameScales
open Filter Topology

/-- Any diverging extra logarithmic factor beats every fixed polynomial. -/
theorem polynomial_exp_tail_tendsto_zero (A : ℕ) {c : ℝ} (hc : 0<c)
    {f : ℕ → ℝ} (hf : Tendsto f atTop atTop) :
    Tendsto (fun N : ℕ => (N:ℝ)^A * Real.exp (-c*L1 N*f N)) atTop (nhds 0) := by
  have hu : Tendsto (fun N => Real.exp (-L1 N)) atTop (nhds 0) :=
    Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp L1_tendsto)
  apply squeeze_zero' _ _ hu
  · exact Filter.Eventually.of_forall fun N => mul_nonneg (pow_nonneg (Nat.cast_nonneg _) _) (Real.exp_pos _).le
  · filter_upwards [eventual_range, (hf.const_mul_atTop hc).eventually
      (eventually_ge_atTop ((A:ℝ)+1)), eventually_gt_atTop (0:ℕ)] with N hN hfN hpos
    have hn : 0<(N:ℝ) := Nat.cast_pos.mpr hpos
    rw [←Real.rpow_natCast,Real.rpow_def_of_pos hn,←Real.exp_add]
    apply Real.exp_le_exp.mpr
    change L1 N*(A:ℝ) + -c*L1 N*f N ≤ -L1 N
    nlinarith [mul_le_mul_of_nonneg_left hfN hN.1.le]

/-- Polynomially many root-link events still have vanishing total error. -/
theorem root_tail_tendsto_zero (A : ℕ) {c : ℝ} (hc : 0<c) :
    Tendsto (fun N : ℕ => (N:ℝ)^A *
      Real.exp (-c*L1 N*Real.log (L3 N))) atTop (nhds 0) :=
  polynomial_exp_tail_tendsto_zero A hc (Real.tendsto_log_atTop.comp L3_tendsto)

/-- Polynomially many candidate-balance events have vanishing total error. -/
theorem candidate_tail_tendsto_zero (A : ℕ) {rate : ℝ} (hrate : 0<rate) :
    Tendsto (fun N : ℕ => (N:ℝ)^A * CandidateBalance.errorBound N rate)
      atTop (nhds 0) :=
  polynomial_exp_tail_tendsto_zero A hrate
    ((tendsto_rpow_atTop (by norm_num : (0:ℝ)<99/100)).comp L3_tendsto)

lemma eventually_rho_small : ∀ᶠ N in atTop, 0<rho N ∧ rho N≤1/8 := by
  filter_upwards [eventual_range, rho_tendsto_zero.eventually
    (gt_mem_nhds (by norm_num : (0:ℝ)<1/8))] with N hN hsmall
  exact ⟨hN.2.2.2.2.2.2.1,hsmall.le⟩

lemma log_rho {N : ℕ} (h3 : 0<L3 N) :
    Real.log (rho N) = -Real.log (L3 N)/800 := by
  dsimp [rho,alpha]
  rw [Real.log_rpow (Real.rpow_pos_of_pos h3 _),Real.log_rpow h3]
  ring

/-- The threshold is independent of the root degree; only its logarithmic
lower bound is used. The exponent is the real-valued binomial-tail exponent. -/
theorem eventually_root_power_bound {c : ℝ} (_hc : 0<c) :
    ∀ᶠ N in atTop, ∀ q : ℕ, c*L1 N≤(q:ℝ) →
      (8*rho N)^((q:ℝ)/4) ≤
        Real.exp (-(c/6400)*L1 N*Real.log (L3 N)) := by
  have hh := (Real.tendsto_log_atTop.comp L3_tendsto).eventually
    (eventually_ge_atTop (1600*Real.log 8))
  filter_upwards [eventual_range,hh] with N hN hlarge q hq
  change 1600*Real.log 8≤Real.log (L3 N) at hlarge
  have h3 : 0<L3 N := by linarith [hN.2.2.1]
  have hr : 0<rho N := hN.2.2.2.2.2.2.1
  have hlog : 0≤Real.log (L3 N) := (Real.log_pos hN.2.2.1).le
  rw [Real.rpow_def_of_pos (mul_pos (by norm_num) hr),
    Real.log_mul (by norm_num : (8:ℝ)≠0) hr.ne',log_rho h3]
  apply Real.exp_le_exp.mpr
  have hcoef : Real.log 8 - Real.log (L3 N)/800 ≤ -Real.log (L3 N)/1600 := by linarith
  have hmul := mul_le_mul_of_nonneg_right hcoef (show 0≤(q:ℝ)/4 by positivity)
  have hq' := mul_le_mul_of_nonneg_right hq hlog
  nlinarith

end LooseHamilton.FrameScales
