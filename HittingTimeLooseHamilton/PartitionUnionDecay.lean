module

public import HittingTimeLooseHamilton.ExceptionalSetAsymptotics
public import Mathlib

public section

/-! Exponential partition concentration is summable over all subsets and times. -/
noncomputable section
namespace LooseHamilton
open Filter Topology

@[expose] def partitionUnionError (r : ℕ) (c : ℝ) (n : ℕ) : ℝ :=
  (2:ℝ)^n * (n:ℝ)^r *
    Real.exp (-c*(n:ℝ)*(Real.log n)^(3/4:ℝ)+(n:ℝ)^(1/10:ℝ))

lemma partitionUnionError_tendsto (r : ℕ) {c : ℝ} (hc : 0<c) :
    Tendsto (partitionUnionError r c) atTop (𝓝 0) := by
  have hlog : Tendsto (fun n : ℕ => Real.log (n:ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hlogpow : Tendsto (fun n : ℕ => (Real.log (n:ℝ))^(3/4:ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0:ℝ)<3/4)).comp hlog
  have hupper : ∀ᶠ n : ℕ in atTop, partitionUnionError r c n ≤ Real.exp (-(n:ℝ)) := by
    filter_upwards [eventually_ge_atTop (1:ℕ),
      hlogpow.eventually (eventually_ge_atTop ((r+4:ℝ)/c))] with n hn hp
    have hn0 : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
    have hn1 : (1:ℝ)≤n := by exact_mod_cast hn
    have hlogle : Real.log (n:ℝ) ≤ n := (Real.log_le_sub_one_of_pos hn0).trans (by linarith)
    have hpow : (n:ℝ)^(1/10:ℝ) ≤ n := by
      simpa using Real.rpow_le_rpow_of_exponent_le hn1 (by norm_num : (1/10:ℝ)≤1)
    have h2 : Real.log (2:ℝ) ≤ 2 := (Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)).trans (by norm_num)
    have heq : partitionUnionError r c n =
        Real.exp ((n:ℝ)*Real.log 2+(r:ℝ)*Real.log n-
          c*(n:ℝ)*(Real.log n)^(3/4:ℝ)+(n:ℝ)^(1/10:ℝ)) := by
      unfold partitionUnionError
      rw [show (2:ℝ)^n=Real.exp ((n:ℝ)*Real.log 2) by rw [Real.exp_nat_mul,Real.exp_log (by norm_num)],
        show (n:ℝ)^r=Real.exp ((r:ℝ)*Real.log n) by rw [Real.exp_nat_mul,Real.exp_log hn0],
        ←Real.exp_add,←Real.exp_add]
      congr 1
      ring
    rw [heq]
    apply Real.exp_le_exp.mpr
    have hcp := (div_le_iff₀ hc).mp hp
    nlinarith [mul_le_mul_of_nonneg_left hlogle (Nat.cast_nonneg r),
      mul_le_mul_of_nonneg_left h2 hn0.le,
      mul_le_mul_of_nonneg_left hcp hn0.le]
  have hexp : Tendsto (fun n : ℕ => Real.exp (-(n:ℝ))) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp tendsto_natCast_atTop_atTop)
  exact squeeze_zero' (Eventually.of_forall (fun n => by unfold partitionUnionError; positivity)) hupper hexp
end LooseHamilton
