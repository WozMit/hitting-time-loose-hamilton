module

public import HittingTimeLooseHamilton.FramePreservationScales

public section

noncomputable section
namespace LooseHamilton.FrameScales
open Filter Topology

lemma eventually_inverse_vertices_le_survival :
    ∀ᶠ (N : ℕ) in atTop, 1/(N:ℝ) ≤ Real.exp (-2*nu N) := by
  filter_upwards [eventual_range, eventually_gt_atTop (0:ℕ)] with N h hN
  have h21 := Real.log_le_sub_one_of_pos h.1
  have h32 := Real.log_le_sub_one_of_pos h.2.1
  change L2 N ≤ L1 N-1 at h21
  change L3 N ≤ L2 N-1 at h32
  have hn : 2*nu N ≤ L1 N := by dsimp [nu]; linarith [h.2.2.1]
  have he := Real.exp_le_exp.mpr (neg_le_neg hn)
  simpa only [L1, neg_mul, Real.exp_neg, Real.exp_log (Nat.cast_pos.mpr hN), one_div] using he

/-- Any fixed coefficient times N^r times the tiny cutoff is smaller than
the survival factor, uniformly for sufficiently large N. -/
lemma eventually_tiny_polynomial_survival (r : ℕ) (hr : 1 ≤ r) (C : ℝ) :
    ∀ᶠ (N : ℕ) in atTop,
      C*(N:ℝ)^r*(N:ℝ)^(-(100*r:ℕ):ℝ) ≤ Real.exp (-2*nu N) := by
  have hex : (r:ℝ)+1-(100*r:ℕ) < 0 := by
    push_cast
    have hr' : (1:ℝ)≤r := by exact_mod_cast hr
    linarith
  have ht := (tendsto_rpow_neg_atTop (neg_pos.mpr hex)).comp tendsto_natCast_atTop_atTop
  simp only [neg_neg] at ht
  have htC := ht.const_mul C
  simp only [mul_zero] at htC
  filter_upwards [htC.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1)),
    eventually_inverse_vertices_le_survival, eventually_gt_atTop (0:ℕ)] with N h hs hN
  have hp : (0:ℝ)<N := Nat.cast_pos.mpr hN
  have he : C*(N:ℝ)^r*(N:ℝ)^(-(100*r:ℕ):ℝ)*(N:ℝ) =
      C*(N:ℝ)^((r:ℝ)+1-(100*r:ℕ)) := by
    rw [← Real.rpow_natCast]
    calc
      _ = C*((N:ℝ)^(r:ℝ)*(N:ℝ)^(-(100*r:ℕ):ℝ)*(N:ℝ)^(1:ℝ)) := by rw [Real.rpow_one]; ring
      _ = C*(N:ℝ)^((r:ℝ)+(-(100*r:ℕ):ℝ)+1) := by rw [← Real.rpow_add hp, ← Real.rpow_add hp]
      _ = _ := by congr 2; ring
  have hh : C*(N:ℝ)^r*(N:ℝ)^(-(100*r:ℕ):ℝ) ≤ 1/(N:ℝ) := by
    apply (le_div_iff₀ hp).2
    rw [he]
    exact h.le
  exact hh.trans hs

end LooseHamilton.FrameScales
