module

public import HittingTimeLooseHamilton.FrameConcentrationScales

public section

noncomputable section
namespace LooseHamilton.FrameScales
open Filter Topology

lemma inv_alpha_le_L3 (N : ℕ) (h : 1 < L3 N) : 1 / alpha N ≤ L3 N := by
  rw [alpha, one_div, ← Real.rpow_neg (by linarith : 0 ≤ L3 N)]
  norm_num
  exact (Real.rpow_le_rpow_of_exponent_le h.le (by norm_num : (1/100:ℝ)≤1)).trans_eq (Real.rpow_one _)

lemma inverse_log_div_alpha_tendsto_zero :
    Tendsto (fun N => (1/L1 N)/alpha N) atTop (nhds 0) := by
  have ht := Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp L1_tendsto
  apply squeeze_zero' _ _ ht
  · filter_upwards [eventual_range] with N h
    exact div_nonneg (div_nonneg (by norm_num) h.1.le) h.2.2.2.1.le
  · filter_upwards [eventual_range] with N h
    have h32 : L3 N ≤ L2 N := by
      have := Real.log_le_sub_one_of_pos h.2.1
      change Real.log (L2 N) ≤ L2 N
      linarith
    have hi := (inv_alpha_le_L3 N h.2.2.1).trans h32
    have hd := div_le_div_of_nonneg_right hi h.1.le
    change 1/L1 N/alpha N ≤ L2 N/L1 N
    convert hd using 1 <;> ring

lemma normalization_error_div_alpha_tendsto_zero :
    Tendsto (fun N => (nu N/(N:ℝ)+1/L1 N)/alpha N) atTop (nhds 0) := by
  simpa only [← add_div, zero_add] using
    nu_div_vertices_div_alpha_tendsto_zero.add inverse_log_div_alpha_tendsto_zero

lemma eventually_normalization_error (A ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N in atTop, A*(nu N/(N:ℝ)+1/L1 N) ≤ ε*alpha N := by
  have ht := normalization_error_div_alpha_tendsto_zero.const_mul A
  simp only [mul_zero] at ht
  filter_upwards [ht.eventually (gt_mem_nhds hε), eventual_range] with N h hR
  apply (div_le_iff₀ hR.2.2.2.1).mp
  convert h.le using 1 <;> ring

lemma nu_mul_log_div_vertices_tendsto_zero :
    Tendsto (fun N => nu N*L1 N/(N:ℝ)) atTop (nhds 0) := by
  have ht := (isLittleO_log_rpow_rpow_atTop (2:ℝ) (by norm_num : (0:ℝ)<1)).tendsto_div_nhds_zero.comp tendsto_natCast_atTop_atTop
  simp only [Real.rpow_two, Real.rpow_one] at ht
  apply squeeze_zero' _ _ ht
  · filter_upwards [eventual_range] with N h
    exact div_nonneg (mul_nonneg h.2.2.2.2.2.1.le h.1.le) (Nat.cast_nonneg _)
  · filter_upwards [eventual_range] with N h
    have h21 := Real.log_le_sub_one_of_pos h.1
    have h32 := Real.log_le_sub_one_of_pos h.2.1
    have hn : nu N ≤ L1 N := by
      change L2 N ≤ L1 N-1 at h21
      change L3 N ≤ L2 N-1 at h32
      dsimp [nu]
      linarith [h.2.2.1]
    change nu N*L1 N/(N:ℝ) ≤ L1 N^2/(N:ℝ)
    exact div_le_div_of_nonneg_right (by nlinarith [mul_le_mul_of_nonneg_right hn h.1.le]) (Nat.cast_nonneg N : (0:ℝ)≤N)

/-- Uniform partition-loss envelope, with the threshold before the active size n. -/
lemma eventually_partition_loss_envelope (A C : ℝ) (hC : 0 < C) :
    ∀ᶠ N in atTop, ∀ n : ℕ, n ≤ N → 1 ≤ Real.log (n:ℝ) →
      A*nu N/(N:ℝ) ≤ C*(Real.log (n:ℝ))^(-1/8:ℝ) := by
  have ht := nu_mul_log_div_vertices_tendsto_zero.const_mul A
  simp only [mul_zero] at ht
  filter_upwards [ht.eventually (gt_mem_nhds hC), eventual_range] with N h hR n hn hlog
  have hnpos : (0:ℝ)<n := by
    by_contra hh
    have hz : (n:ℝ)=0 := le_antisymm (le_of_not_gt hh) (Nat.cast_nonneg _)
    rw [hz, Real.log_zero] at hlog
    linarith
  have hlogN : Real.log (n:ℝ) ≤ L1 N :=
    Real.strictMonoOn_log.monotoneOn hnpos (hnpos.trans_le (Nat.cast_le.mpr hn)) (Nat.cast_le.mpr hn)
  have hi : 1/L1 N ≤ (Real.log (n:ℝ))^(-1/8:ℝ) := by
    calc
      _ ≤ 1/Real.log (n:ℝ) := one_div_le_one_div_of_le (by linarith) hlogN
      _ = (Real.log (n:ℝ))^(-1:ℝ) := by rw [Real.rpow_neg_one, one_div]
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hlog (by norm_num)
  have hh : A*nu N/(N:ℝ) ≤ C/L1 N := by
    apply (le_div_iff₀ hR.1).2
    convert h.le using 1 <;> ring
  exact hh.trans (by simpa only [mul_one_div] using mul_le_mul_of_nonneg_left hi hC.le)

end LooseHamilton.FrameScales
