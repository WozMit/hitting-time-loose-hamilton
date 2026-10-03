module

public import HittingTimeLooseHamilton.FrameSurvivalRates
public import HittingTimeLooseHamilton.FrameSurvivalRatios
public import Mathlib.Analysis.SpecificLimits.Basic

public section

noncomputable section
open Filter
namespace LooseHamilton.FrameSurvival

@[expose] def batchSize (m k : ℕ) (ν : ℝ) : ℕ := ⌊ν*m/k⌋₊

lemma batchSize_le (m k : ℕ) (ν : ℝ) (hν : 0 ≤ ν) :
    (batchSize m k ν:ℝ) ≤ ν*m/k := Nat.floor_le (by positivity)

lemma batch_feasible_finite (N m k : ℕ) (ν a b r : ℝ)
    (hN : 0 < (N:ℝ)) (ha : 0 < a) (hb : 0 < b) (hr : 0 < r)
    (hNk : (N:ℝ) ≤ a*k) (hkN : (k:ℝ) ≤ b*N)
    (hν : 1 ≤ ν) (hsmall : ν/(N:ℝ) ≤ 1/(4*a))
    (hdense : 4*b*r ≤ r*m/N) :
    0 < m ∧ 1 ≤ k ∧ 1 ≤ batchSize m k ν ∧
      4*k ≤ m ∧ 4*batchSize m k ν ≤ m := by
  have hkpos : 0 < (k:ℝ) := by nlinarith
  have hmpos : 0 < (m:ℝ) := by
    by_contra h
    have hm0 : (m:ℝ)=0 := le_antisymm (not_lt.mp h) (by positivity)
    simp only [hm0, mul_zero, zero_div] at hdense
    nlinarith [mul_pos hb hr]
  have h4k : 4*(k:ℝ) ≤ m := by
    have hd := (le_div_iff₀ hN).mp hdense
    nlinarith [mul_nonneg hr.le (sub_nonneg.mpr hkN)]
  have hνN : 4*a*ν ≤ (N:ℝ) := by
    have hh := (div_le_div_iff₀ hN (show 0 < 4*a by positivity)).mp hsmall
    nlinarith
  have h4ν : 4*ν ≤ (k:ℝ) := by nlinarith
  have hfloor := batchSize_le m k ν (by linarith)
  have h4t : 4*(batchSize m k ν:ℝ) ≤ m := by
    have hh := (le_div_iff₀ hkpos).mp hfloor
    nlinarith [mul_nonneg hmpos.le (sub_nonneg.mpr h4ν)]
  have ht1 : 1 ≤ batchSize m k ν := by
    apply (Nat.le_floor_iff (by positivity : 0 ≤ ν*(m:ℝ)/k)).mpr
    apply (le_div_iff₀ hkpos).mpr
    norm_num
    nlinarith
  exact ⟨by exact_mod_cast hmpos, by exact_mod_cast hkpos, ht1,
    by exact_mod_cast h4k, by exact_mod_cast h4t⟩

/-- The asymptotic assumptions imply batch feasibility; quarter bounds are conclusions. -/
theorem batch_eventually_feasible (N m k : ℕ → ℕ) (ν : ℕ → ℝ)
    (a b r : ℝ) (ha : 0 < a) (hb : 0 < b) (hr : 0 < r)
    (hN : Tendsto (fun i => (N i:ℝ)) atTop atTop)
    (hμ : Tendsto (fun i => r*m i/N i) atTop atTop)
    (hν : Tendsto ν atTop atTop)
    (hνN : Tendsto (fun i => ν i/N i) atTop (nhds 0))
    (hcomp : ∀ᶠ i in atTop, (N i:ℝ) ≤ a*k i ∧ (k i:ℝ) ≤ b*N i) :
    ∀ᶠ i in atTop, 0 < m i ∧ 1 ≤ k i ∧ 1 ≤ batchSize (m i) (k i) (ν i) ∧
      4*k i ≤ m i ∧ 4*batchSize (m i) (k i) (ν i) ≤ m i := by
  have hs := hνN.eventually (gt_mem_nhds (show (0:ℝ)<1/(4*a) by positivity))
  filter_upwards [hN.eventually (eventually_gt_atTop (0:ℝ)),
    hμ.eventually (eventually_ge_atTop (4*b*r)),
    hν.eventually (eventually_ge_atTop (1:ℝ)), hs, hcomp] with i hn hm hv hs hc
  exact batch_feasible_finite (N i) (m i) (k i) (ν i) a b r
    hn ha hb hr hc.1 hc.2 hv hs.le hm

/-- Both printed survival asymptotics for the actual floored batch, including
conditioning on deletion of the candidate edge. -/
theorem batch_survival_asymptotics (N m k : ℕ → ℕ) (ν : ℕ → ℝ)
    (a b r : ℝ) (ha : 0 < a) (hb : 0 < b) (hr : 0 < r)
    (hN : Tendsto (fun i => (N i:ℝ)) atTop atTop)
    (hμ : Tendsto (fun i => r*m i/N i) atTop atTop)
    (hν : Tendsto ν atTop atTop)
    (hνN : Tendsto (fun i => ν i/N i) atTop (nhds 0))
    (hcomp : ∀ᶠ i in atTop, (N i:ℝ) ≤ a*k i ∧ (k i:ℝ) ≤ b*N i) :
    Asymptotics.IsBigO atTop
      (fun i => zeta (m i) (batchSize (m i) (k i) (ν i)) (k i-1) /
        zeta (m i) (batchSize (m i) (k i) (ν i)) (k i)-1)
      (fun i => ν i/N i) ∧
    Asymptotics.IsBigO atTop
      (fun i => conditionedZeta (m i) (batchSize (m i) (k i) (ν i)) (k i) /
        zeta (m i) (batchSize (m i) (k i) (ν i)) (k i)-1)
      (fun i => 1/(r*m i/N i)+ν i/N i) := by
  have hf := batch_eventually_feasible N m k ν a b r ha hb hr hN hμ hν hνN hcomp
  have hdata : ∀ᶠ i in atTop,
      0 < (N i:ℝ) ∧ 0 ≤ ν i ∧ (N i:ℝ) ≤ a*k i ∧ (k i:ℝ) ≤ b*N i ∧
      0 < m i ∧ 1 ≤ k i ∧ 1 ≤ batchSize (m i) (k i) (ν i) ∧
      4*k i ≤ m i ∧ 4*batchSize (m i) (k i) (ν i) ≤ m i := by
    filter_upwards [hN.eventually (eventually_gt_atTop (0:ℝ)),
      hν.eventually (eventually_ge_atTop (0:ℝ)), hcomp, hf] with i hn hv hc hf
    exact ⟨hn,hv,hc.1,hc.2,hf⟩
  constructor
  · apply Asymptotics.IsBigO.of_bound (2*a)
    filter_upwards [hdata] with i hi
    rcases hi with ⟨hn,hv,hnk,hkn,hm,hk,ht,hk4,ht4⟩
    have hmR : 0 < (m i:ℝ) := by exact_mod_cast hm
    have hkR : 0 < (k i:ℝ) := by exact_mod_cast (show 0<k i by omega)
    have hk4R : 4*(k i:ℝ) ≤ m i := by exact_mod_cast hk4
    have ht4R : 4*(batchSize (m i) (k i) (ν i):ℝ) ≤ m i := by exact_mod_cast ht4
    have hh := frame_survival_ratio_rate (m i) (k i) (batchSize (m i) (k i) (ν i))
      (N i) (ν i) a hmR hkR hn hv (by positivity) hk4R ht4R
      (batchSize_le _ _ _ hv) hnk
    rw [completion_ratio hk (by omega) (by omega)]
    simpa only [Real.norm_eq_abs, abs_of_nonneg (div_nonneg hv hn.le)] using hh
  · apply Asymptotics.IsBigO.of_bound (2*b*r+2*a)
    filter_upwards [hdata] with i hi
    rcases hi with ⟨hn,hv,hnk,hkn,hm,hk,ht,hk4,ht4⟩
    have hmR : 0 < (m i:ℝ) := by exact_mod_cast hm
    have hkR : 1 ≤ (k i:ℝ) := by exact_mod_cast hk
    have hk4R : 4*(k i:ℝ) ≤ m i := by exact_mod_cast hk4
    have ht4R : 4*(batchSize (m i) (k i) (ν i):ℝ) ≤ m i := by exact_mod_cast ht4
    have hmu : 0 < r*m i/N i := by positivity
    have hh := frame_deleted_survival_ratio_rate (m i) (k i) (batchSize (m i) (k i) (ν i))
      (N i) (ν i) a b r (r*m i/N i) hmR hkR hn hv (by positivity) hk4R ht4R
      (batchSize_le _ _ _ hv) hnk hkn hmu rfl
    rw [conditioned_completion_ratio hk ht (by omega)]
    have hq : 0 ≤ ν i/N i := div_nonneg hv hn.le
    have hp : 0 ≤ 1/(r*m i/N i) := by positivity
    simp only [Real.norm_eq_abs, abs_of_nonneg (add_nonneg hp hq)]
    have heq : 2*b*r/(r*m i/N i) = (2*b*r)*(1/(r*m i/N i)) := by ring
    rw [heq] at hh
    nlinarith [mul_nonneg (show 0 ≤ 2*b*r by positivity) hq,
      mul_nonneg (show 0 ≤ 2*a by positivity) hp]

end LooseHamilton.FrameSurvival
