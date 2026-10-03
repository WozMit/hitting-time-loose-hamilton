module

public import HittingTimeLooseHamilton.TerminalLowSetScales

public section

/-! The exponential low-set union bound survives terminal conditioning. -/
noncomputable section
set_option maxHeartbeats 1000000
namespace LooseHamilton
open Filter Topology

lemma choose_le_exp_entropy (n t : ℕ) (hn : 0<n) (ht : 0<t) :
    (n.choose t:ℝ) ≤ Real.exp ((t:ℝ)*(1+Real.log ((n:ℝ)/t))) := by
  have hn0 : (0:ℝ)<n := by exact_mod_cast hn
  have ht0 : (0:ℝ)<t := by exact_mod_cast ht
  calc
    (n.choose t:ℝ) ≤ (n:ℝ)^t/(t.factorial:ℝ) := Nat.choose_le_pow_div t n
    _ = ((n:ℝ)/t)^t*((t:ℝ)^t/t.factorial) := by rw [div_pow]; field_simp
    _ ≤ ((n:ℝ)/t)^t*Real.exp (t:ℝ) :=
      mul_le_mul_of_nonneg_left (Real.pow_div_factorial_le_exp (t:ℝ) ht0.le t) (by positivity)
    _ = Real.exp ((t:ℝ)*(1+Real.log ((n:ℝ)/t))) := by
      rw [mul_add, mul_one, Real.exp_add,
        Real.exp_nat_mul, Real.exp_log (div_pos hn0 ht0), mul_comm]

lemma terminalLowSet_choose_eventually :
    ∀ᶠ n : ℕ in atTop, (n.choose (terminalLowSetSize n):ℝ) ≤
      Real.exp ((76/100:ℝ)*(terminalLowSetSize n:ℝ)*Real.log n) := by
  have hlog : Tendsto (fun n : ℕ => Real.log (n:ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_ge_atTop (1:ℕ),hlog.eventually (eventually_ge_atTop 100)] with n hn hl
  have hn0 : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
  have hp := Real.rpow_pos_of_pos hn0 (1/4:ℝ)
  have hsize : (n:ℝ)^(1/4:ℝ) ≤ (terminalLowSetSize n:ℝ) := Nat.le_ceil _
  have ht0 : (0:ℝ)<terminalLowSetSize n := hp.trans_le hsize
  have hlogt : (1/4:ℝ)*Real.log (n:ℝ) ≤ Real.log (terminalLowSetSize n:ℝ) := by
    simpa [Real.log_rpow hn0] using Real.log_le_log hp hsize
  have hratio : Real.log ((n:ℝ)/(terminalLowSetSize n:ℝ)) ≤ (3/4:ℝ)*Real.log n := by
    rw [Real.log_div (ne_of_gt hn0) (ne_of_gt ht0)]
    linarith
  apply (choose_le_exp_entropy n (terminalLowSetSize n) (by omega) (by exact_mod_cast ht0)).trans
  apply Real.exp_le_exp.mpr
  have hbase : 1+Real.log ((n:ℝ)/(terminalLowSetSize n:ℝ)) ≤ (76/100:ℝ)*Real.log n := by linarith
  nlinarith [mul_le_mul_of_nonneg_left hbase ht0.le]

/-- A single error function sufficient after the feasibility denominator. -/
@[expose] def terminalLowSetError (n : ℕ) : ℝ := 2*Real.exp (-(n:ℝ)^(1/10:ℝ))

lemma terminalLowSetError_tendsto : Tendsto terminalLowSetError atTop (𝓝 0) := by
  have hpow : Tendsto (fun n : ℕ => (n:ℝ)^(1/10:ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0:ℝ)<1/10)).comp tendsto_natCast_atTop_atTop
  have hneg : Tendsto (fun n : ℕ => -((n:ℝ)^(1/10:ℝ))) atTop atBot :=
    tendsto_neg_atTop_atBot.comp hpow
  have he : Tendsto (fun n : ℕ => Real.exp (-((n:ℝ)^(1/10:ℝ)))) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp hneg
  have hh := he.const_mul 2
  simp only [mul_zero] at hh
  exact hh

lemma terminalLowSet_conditioned_bound_eventually {r : ℕ} (hr : 1 ≤ r) :
    ∀ᶠ n : ℕ in atTop, ∀ M : ℕ,
      |(r:ℝ)*M/n-Real.log n| ≤ 3*Real.log (Real.log n) →
      Real.exp ((n:ℝ)^(1/10:ℝ))*
        ((n.choose (terminalLowSetSize n):ℝ)*
          Real.exp (-(82/100:ℝ)*(terminalLowSetSize n:ℝ)*Real.log n)+
          Real.exp (-(M:ℝ)/1010000)) ≤ terminalLowSetError n := by
  have hr0 : (0:ℝ)<r := by exact_mod_cast (show 0<r by omega)
  have hsmall := tendsto_nat_rpow_ratio (by norm_num : (1/10:ℝ)<1/4)
  have hlin := tendsto_nat_rpow_ratio (by norm_num : (1/10:ℝ)<1)
  filter_upwards [terminalLowSet_choose_eventually,eventually_feasibility_parameters 0,
    eventually_ge_atTop (1:ℕ),
    (tendsto_order.mp hsmall).2 (3/100) (by norm_num),
    (tendsto_order.mp hlin).2 (1/(4*(r:ℝ)*1010000)) (by positivity)]
      with n hc hp hn hs hlin
  intro M hM
  have hn0 : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
  have hq : (0:ℝ)<(n:ℝ)^(1/4:ℝ) := Real.rpow_pos_of_pos hn0 _
  have ht : (n:ℝ)^(1/4:ℝ) ≤ (terminalLowSetSize n:ℝ) := Nat.le_ceil _
  have ht0 : (0:ℝ)≤terminalLowSetSize n := Nat.cast_nonneg _
  have hmul := (div_lt_iff₀ hq).mp hs
  have hlog := hp.1
  have hmain : (n.choose (terminalLowSetSize n):ℝ)*
      Real.exp (-(82/100:ℝ)*(terminalLowSetSize n:ℝ)*Real.log n) ≤
      Real.exp (-2*(n:ℝ)^(1/10:ℝ)) := by
    calc
      _ ≤ Real.exp ((76/100:ℝ)*(terminalLowSetSize n:ℝ)*Real.log n)*
          Real.exp (-(82/100:ℝ)*(terminalLowSetSize n:ℝ)*Real.log n) :=
        mul_le_mul_of_nonneg_right hc (Real.exp_pos _).le
      _ ≤ _ := by
        rw [←Real.exp_add]
        apply Real.exp_le_exp.mpr
        nlinarith [mul_le_mul_of_nonneg_left hlog ht0]
  have hmean := hp.2.1 ((r:ℝ)*M/n) hM
  have hmean' := (le_div_iff₀ hn0).mp hmean
  have hMlin : (n:ℝ)/2 ≤ (r:ℝ)*M := by nlinarith
  rw [Real.rpow_one] at hlin
  have hscale := (div_lt_div_iff₀ hn0 (show (0:ℝ)<4*r*1010000 by positivity)).mp hlin
  have hoverflow : Real.exp (-(M:ℝ)/1010000) ≤ Real.exp (-2*(n:ℝ)^(1/10:ℝ)) := by
    apply Real.exp_le_exp.mpr
    have : 2*(n:ℝ)^(1/10:ℝ) ≤ (M:ℝ)/1010000 := by
      apply (le_div_iff₀ (by norm_num : (0:ℝ)<1010000)).mpr
      apply (mul_le_mul_iff_right₀ hr0).mp
      nlinarith
    linarith
  calc
    _ ≤ Real.exp ((n:ℝ)^(1/10:ℝ)) *
        (Real.exp (-2*(n:ℝ)^(1/10:ℝ))+Real.exp (-2*(n:ℝ)^(1/10:ℝ))) := by
      gcongr
    _ = terminalLowSetError n := by
      unfold terminalLowSetError
      rw [mul_add,←Real.exp_add]
      rw [show (n:ℝ)^(1/10:ℝ)+ -2*(n:ℝ)^(1/10:ℝ) = -(n:ℝ)^(1/10:ℝ) by ring]
      ring
end LooseHamilton
