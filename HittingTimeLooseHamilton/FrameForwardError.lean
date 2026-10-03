module

public import HittingTimeLooseHamilton.FramePersistenceScales
public import HittingTimeLooseHamilton.NoDeficitScales
public import HittingTimeLooseHamilton.NoDeficitModels

public section

noncomputable section
namespace LooseHamilton.FrameScales
open Filter Topology

/-- The terminal no-deficit error evaluated at the prescribed batch scale. -/
lemma terminal_error_tendsto_zero {A : ℝ} (hA : 0≤A) :
    Tendsto (fun N => noDeficitError A (epsilon/8) N (nu N)) atTop (nhds 0) := by
  have hp : Tendsto (fun N => A*nu N*(N:ℝ)^(-3/4:ℝ)*Real.log N)
      atTop (nhds 0) := by
    apply squeeze_zero' _ _ (noDeficit_protected_error_tendsto_zero A)
    · filter_upwards [eventual_range] with N h
      exact mul_nonneg (mul_nonneg (mul_nonneg hA h.2.2.2.2.2.1.le)
        (Real.rpow_nonneg (Nat.cast_nonneg _) _)) h.1.le
    · filter_upwards [eventual_range] with N h
      have h21 := Real.log_le_sub_one_of_pos h.1
      have h32 := Real.log_le_sub_one_of_pos h.2.1
      change L2 N ≤ L1 N-1 at h21
      change L3 N ≤ L2 N-1 at h32
      have hn : nu N ≤ L1 N := by dsimp [nu]; linarith [h.2.2.1]
      have hh := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hn hA)
        (mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg N) (-3/4:ℝ)) h.1.le)
      change A*nu N*(N:ℝ)^(-3/4:ℝ)*L1 N ≤ A*(N:ℝ)^(-3/4:ℝ)*L1 N^2
      nlinarith [hh]
  simpa only [noDeficitError, zero_add, neg_div] using hp.add noDeficit_exponential_error_tendsto_zero

/-- A single error bound chosen before the frame, source, exposure record,
and batch. The three probability arguments retain their separate constants. -/
@[expose] def forwardError (r : ℕ) (C Km Kc Kg : ℝ) (N : ℕ) : ℝ :=
  noDeficitError (C*(8*((r:ℝ)-1))) (epsilon/8) N (nu N) +
  survivalFailureBound Km N + survivalFailureBound Kc N/(alpha N)^2 +
  Kg*((1/(alpha N*Real.sqrt (L2 N))+survivalFailureBound 1 N)/(alpha N)^2)

lemma forwardError_eventually_nonneg {r : ℕ} (hr : 1≤r) {C Km Kc Kg : ℝ}
    (hC : 0≤C) (hKm : 0≤Km) (hKc : 0≤Kc) (hKg : 0≤Kg) :
    ∀ᶠ N in atTop, 0≤forwardError r C Km Kc Kg N := by
  filter_upwards [eventual_range] with N h
  have hr' : (1:ℝ)≤r := by exact_mod_cast hr
  have hterm : 0≤noDeficitError (C*(8*((r:ℝ)-1))) (epsilon/8) N (nu N) := by
    unfold noDeficitError
    exact add_nonneg (mul_nonneg (mul_nonneg (mul_nonneg
      (mul_nonneg hC (by linarith)) h.2.2.2.2.2.1.le)
      (Real.rpow_nonneg (Nat.cast_nonneg _) _)) h.1.le) (Real.exp_pos _).le
  unfold forwardError
  exact add_nonneg (add_nonneg (add_nonneg hterm
    (survivalFailureBound_nonneg hKm N h.2.1.le))
    (div_nonneg (survivalFailureBound_nonneg hKc N h.2.1.le) (sq_nonneg _)))
    (mul_nonneg hKg (sampledRoleTailBound_nonneg (by norm_num) (by norm_num)
      N h.2.2.2.1.le h.2.1.le))

lemma forwardError_tendsto_zero {r : ℕ} (hr : 1≤r) {C Km Kc Kg : ℝ}
    (hC : 0≤C) (hKm : 0≤Km) (hKc : 0≤Kc) :
    Tendsto (forwardError r C Km Kc Kg) atTop (nhds 0) := by
  have hr' : (1:ℝ)≤r := by exact_mod_cast hr
  have ht := terminal_error_tendsto_zero (mul_nonneg hC (show 0≤8*((r:ℝ)-1) by linarith))
  have hm := survivalFailureBound_tendsto_zero hKm
  have hc := survivalFailureBound_div_alpha_tendsto hKc 2
  simp only [Real.rpow_two] at hc
  have hg := (sampledRoleTailBound_tendsto_zero 1 (by norm_num : (0:ℝ)≤1)).const_mul Kg
  simp only [mul_zero] at hg
  have h := ((ht.add hm).add hc).add hg
  simp only [sampledRoleTailBound, zero_add] at h
  exact h

/-- Uniform eventual positivity of the success factor used in reverse counting. -/
lemma eventually_forwardError_lt_one {r : ℕ} (hr : 1≤r) {C Km Kc Kg : ℝ}
    (hC : 0≤C) (hKm : 0≤Km) (hKc : 0≤Kc) :
    ∀ᶠ N in atTop, forwardError r C Km Kc Kg N < 1 :=
  (forwardError_tendsto_zero hr hC hKm hKc).eventually (gt_mem_nhds (by norm_num))

end LooseHamilton.FrameScales
