module

public import HittingTimeLooseHamilton.FramePreservationScales
public import HittingTimeLooseHamilton.FrameSurvivalFailureScale

public section

noncomputable section
namespace LooseHamilton.FrameScales
open Filter Topology

lemma inverse_vertices_div_alpha_sq_tendsto_zero :
    Tendsto (fun (N : ℕ) => (1/(N:ℝ))/(alpha N)^2) atTop (nhds 0) := by
  have ht := (isLittleO_log_rpow_rpow_atTop (2:ℝ) (by norm_num : (0:ℝ)<1)).tendsto_div_nhds_zero.comp tendsto_natCast_atTop_atTop
  simp only [Real.rpow_two, Real.rpow_one] at ht
  apply squeeze_zero' _ _ ht
  · filter_upwards [eventual_range] with N h
    exact div_nonneg (div_nonneg (by norm_num) (Nat.cast_nonneg _)) (sq_nonneg _)
  · filter_upwards [eventual_range] with N h
    have h21 := Real.log_le_sub_one_of_pos h.1
    have h32 := Real.log_le_sub_one_of_pos h.2.1
    change L2 N ≤ L1 N-1 at h21
    change L3 N ≤ L2 N-1 at h32
    have hi : 1/alpha N ≤ L1 N := (inv_alpha_le_L3 N h.2.2.1).trans (by linarith)
    have hsq : (1/alpha N)^2 ≤ L1 N^2 := by
      exact pow_le_pow_left₀ (div_nonneg (by norm_num) h.2.2.2.1.le) hi 2
    have hd := div_le_div_of_nonneg_right hsq (Nat.cast_nonneg N : (0:ℝ)≤N)
    change 1/(N:ℝ)/alpha N^2 ≤ L1 N^2/(N:ℝ)
    convert hd using 1 <;> ring

/-- Uniform deterministic boundary loss and the resulting retained fraction. -/
lemma eventually_boundary_fraction_alpha_sq (A : ℝ) :
    ∀ᶠ (N : ℕ) in atTop, A/(N:ℝ) ≤ alpha N^2 ∧
      alpha N-2*alpha N^2 ≥ alpha N/2 := by
  have ht := inverse_vertices_div_alpha_sq_tendsto_zero.const_mul A
  simp only [mul_zero] at ht
  filter_upwards [ht.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1)),
    alpha_tendsto_zero.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1/4)),
    eventual_range] with N h ha hR
  constructor
  · have hs : 0<alpha N^2 := sq_pos_of_pos hR.2.2.2.1
    have hh : (A/(N:ℝ))/alpha N^2 < 1 := by convert h using 1 <;> ring
    have := (div_lt_iff₀ hs).mp hh
    nlinarith
  · nlinarith [hR.2.2.2.1]

/-- Markov loss for sampled abnormal roles, including the conditional
completion failure probability, at threshold alpha². -/
@[expose] def sampledRoleTailBound (A K : ℝ) (N : ℕ) : ℝ :=
  (A/(alpha N*Real.sqrt (L2 N))+survivalFailureBound K N)/alpha N^2

lemma sampledRoleTailBound_nonneg {A K : ℝ} (hA : 0≤A) (hK : 0≤K)
    (N : ℕ) (ha : 0≤alpha N) (hL : 0≤L2 N) :
    0≤sampledRoleTailBound A K N := by
  unfold sampledRoleTailBound
  exact div_nonneg (add_nonneg (div_nonneg hA (mul_nonneg ha (Real.sqrt_nonneg _)))
    (survivalFailureBound_nonneg hK N hL)) (sq_nonneg _)

lemma sampledRoleTailBound_tendsto_zero (A : ℝ) {K : ℝ} (hK : 0≤K) :
    Tendsto (sampledRoleTailBound A K) atTop (nhds 0) := by
  have hs := (static_error_div_alpha_power 2).const_mul A
  have hp := survivalFailureBound_div_alpha_tendsto hK 2
  simp only [Real.rpow_two, mul_zero] at hs hp
  have ht := hs.add hp
  simp only [zero_add] at ht
  convert ht using 1
  funext N
  unfold sampledRoleTailBound
  ring

/-- A single main survival failure plus the role Markov failure. No union
bound over candidates or conditional main-survival event is introduced. -/
@[expose] def persistenceFailureBound (A Kmain Kcompletion : ℝ) (N : ℕ) : ℝ :=
  survivalFailureBound Kmain N + sampledRoleTailBound A Kcompletion N

lemma persistenceFailureBound_tendsto_zero (A : ℝ) {Kmain Kcompletion : ℝ}
    (hKm : 0≤Kmain) (hKc : 0≤Kcompletion) :
    Tendsto (persistenceFailureBound A Kmain Kcompletion) atTop (nhds 0) := by
  change Tendsto (fun N => survivalFailureBound Kmain N + sampledRoleTailBound A Kcompletion N) atTop (nhds 0)
  simpa only [zero_add] using
    (survivalFailureBound_tendsto_zero hKm).add (sampledRoleTailBound_tendsto_zero A hKc)

end LooseHamilton.FrameScales
