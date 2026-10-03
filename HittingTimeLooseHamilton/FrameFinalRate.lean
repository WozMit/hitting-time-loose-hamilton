module

public import HittingTimeLooseHamilton.CandidateBalanceExponential
public import HittingTimeLooseHamilton.FrameForwardError

public section

noncomputable section
namespace LooseHamilton.FrameScales
open Filter Topology

/-- Explicit rate depending only on uniformity, not on the boundary,
regularity constants, entropy budget, time, or exposure record. -/
@[expose] def finalRate (r : ℕ) : ℝ := 1/(204800*(r:ℝ))

lemma finalRate_pos {r : ℕ} (hr : 0<r) : 0<finalRate r := by
  unfold finalRate
  exact div_pos (by norm_num) (mul_pos (by norm_num) (Nat.cast_pos.mpr hr))

lemma batch_exponent_lower {r N : ℕ} (hr : 0<r) (h3 : 0<L3 N)
    (τ : ℝ) (hτ : nu N*L1 N/(16*(r:ℝ))≤τ) :
    L1 N*(L3 N)^(99/100:ℝ)/(102400*(r:ℝ)) ≤ alpha N*τ/64 := by
  have ha : 0≤alpha N := Real.rpow_nonneg h3.le _
  have h := mul_le_mul_of_nonneg_left hτ ha
  have hs := alpha_mul_nu N h3
  have he : alpha N*(nu N*L1 N/(16*(r:ℝ))) =
      L1 N*(L3 N)^(99/100:ℝ)/(1600*(r:ℝ)) := by
    calc
      _ = (alpha N*nu N)*L1 N/(16*(r:ℝ)) := by ring
      _ = _ := by rw [hs]; ring
  rw [he] at h
  have hh := div_le_div_of_nonneg_right h (by norm_num : (0:ℝ)≤64)
  convert hh using 1 <;> ring

/-- A common threshold, chosen before all probabilities, errors, and batch
sizes, absorbs the forward factor into half of the reverse exponent. -/
theorem eventually_final_exponential (r : ℕ) (hr : 0<r) :
    ∀ᶠ N in atTop, ∀ p e τ : ℝ, 0≤p → e≤1/2 →
      nu N*L1 N/(16*(r:ℝ))≤τ →
      (1-e)*p≤Real.exp (-alpha N*τ/64) →
      p≤Real.exp (-finalRate r*L1 N*(L3 N)^(99/100:ℝ)) := by
  have hd : 0<(1:ℝ)/(16*(r:ℝ)) := by positivity
  have hc : 0<(1/64:ℝ) := by norm_num
  have hlarge := (target_exponent_tendsto.const_mul_atTop (finalRate_pos hr)).eventually
    (eventually_ge_atTop (Real.log 2))
  filter_upwards [eventual_range,hlarge] with N hN hL p e τ hp he hτ hf
  have hs : alpha N*(nu N*L1 N) = (L1 N*(L3 N)^(99/100:ℝ))/100 := by
    rw [←mul_assoc,alpha_mul_nu N (by linarith [hN.2.2.1])]
    ring
  have hτ' : (1/(16*(r:ℝ)))*(nu N*L1 N)≤τ := by convert hτ using 1 <;> ring
  have hlarge' : Real.log 2≤(1/64:ℝ)*(1/(16*(r:ℝ)))*(L1 N*(L3 N)^(99/100:ℝ))/200 := by
    convert hL using 1
    unfold finalRate
    ring
  have hf' : (1-e)*p≤Real.exp (-(1/64:ℝ)*alpha N*τ) := by convert hf using 1 <;> congr 1 <;> ring
  have hh := candidate_exponential_scalar hp he hc.le hN.2.2.2.1.le hτ' hs hlarge' hf'
  convert hh using 1
  congr 1
  unfold finalRate
  ring

/-- The complete forward-error function can be absorbed with the same rate;
only the threshold additionally depends on its fixed constants. -/
theorem eventually_forwardError_final_exponential {r : ℕ} (hr : 1≤r)
    {C Km Kc Kg : ℝ} (hC : 0≤C) (hKm : 0≤Km) (hKc : 0≤Kc) :
    ∀ᶠ N in atTop, ∀ p τ : ℝ, 0≤p →
      nu N*L1 N/(16*(r:ℝ))≤τ →
      (1-forwardError r C Km Kc Kg N)*p≤Real.exp (-alpha N*τ/64) →
      p≤Real.exp (-finalRate r*L1 N*(L3 N)^(99/100:ℝ)) := by
  have he := (forwardError_tendsto_zero (Kg:=Kg) hr hC hKm hKc).eventually
    (gt_mem_nhds (by norm_num : (0:ℝ)<1/2))
  filter_upwards [eventually_final_exponential r (by omega),he] with N hN hE p τ hp hτ hf
  exact hN p _ τ hp hE.le hτ hf

end LooseHamilton.FrameScales
