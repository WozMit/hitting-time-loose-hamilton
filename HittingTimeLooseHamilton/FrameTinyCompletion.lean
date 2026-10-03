module

public import HittingTimeLooseHamilton.FrameTinyCompletionFinite
public import HittingTimeLooseHamilton.FrameTinySurvivalLower
public import HittingTimeLooseHamilton.FrameTinyScales

public section

/-! Tiny actual frame completions, using the original vertex count cutoff. -/
noncomputable section
namespace LooseHamilton.AuxiliaryFrame.Frame
open Finset Filter FrameScales

/-- A tiny source completion stays abnormal after deletion whenever the main
count retains half its predicted value. No completion survival event is assumed. -/
theorem tiny_completion_persists_eventually (r : ℕ) (hr : 3≤r) :
    ∀ᶠ N in atTop, ∀ (original : Finset (Finset (Fin N))) (F : Frame r original)
      (H T : Finset (Finset (Fin N))) (c : Finset (Fin N) × Fin N × Fin N)
      (m τ : ℕ),
    0 < m → 4*F.k≤m → 4*τ≤m → (τ:ℝ)*F.k/m≤nu N →
    0 < F.cycleCount H →
    (F.completionCount H c:ℝ) < (F.cycleCount H:ℝ)*(N:ℝ)^(-(100*(r:ℝ))) →
    CandidateLogSurvival.zeta m F.k τ * F.cycleCount H / 2 ≤ F.cycleCount (H\T) →
    candidateNormalizedCount (F.cycleCount (H\T)) (F.completionCount (H\T) c)
      (F.mu (H\T)) (((r:ℝ)-1)^2) ≤ 1/4 ∧
    alpha N/2 < |candidateNormalizedCount (F.cycleCount (H\T))
      (F.completionCount (H\T) c) (F.mu (H\T)) (((r:ℝ)-1)^2) - 1| := by
  filter_upwards [eventually_tiny_polynomial_survival r (by omega) (8*(((r:ℝ)-1)^2)*r),
    eventual_range] with N hcut hR original F H T c m τ hm hk4 ht4 hτ hX hY hmain
  have hcut' : 8*(((r:ℝ)-1)^2)*(r*(N:ℝ)^r)*(N:ℝ)^(-(100*(r:ℝ))) ≤ Real.exp (-2*nu N) := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat, mul_assoc] using hcut
  have hμ : 0 ≤ F.mu (H\T) := by unfold mu; positivity
  have hp : 0 ≤ (N:ℝ)^(-(100*(r:ℝ))) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hbound := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (F.mu_polynomial_upper (H\T))
      (show 0≤8*(((r:ℝ)-1)^2) by positivity)) hp
  simp only [Fintype.card_fin] at hbound
  have hz := CandidateLogSurvival.zeta_ge_exp_neg_two hm hk4 ht4 hτ
  have hn := tiny_completion_normalized_le
    (F.cycleCount H) (F.completionCount H c) (F.cycleCount (H\T))
    (F.completionCount (H\T) c) (F.mu (H\T)) (((r:ℝ)-1)^2)
    (CandidateLogSurvival.zeta m F.k τ) ((N:ℝ)^(-(100*(r:ℝ))))
    (by exact_mod_cast hX) ((Real.exp_pos _).trans_le hz) hY.le
    (by exact_mod_cast F.completionCount_delete_le H T c) hμ (sq_nonneg _)
    (hbound.trans (hcut'.trans hz)) hmain
  refine ⟨hn, ?_⟩
  have ha := neg_le_abs (candidateNormalizedCount (F.cycleCount (H\T))
    (F.completionCount (H\T) c) (F.mu (H\T)) (((r:ℝ)-1)^2) - 1)
  linarith [hR.2.2.2.2.1]

/-- Every source-normal role is above the large-completion cutoff.
The eventual threshold is uniform in all frames, hosts and candidates. -/
theorem source_normal_completion_large_eventually (r : ℕ) (hr : 3≤r) :
    ∀ᶠ N in atTop, ∀ (original : Finset (Finset (Fin N))) (F : Frame r original)
      (H : Finset (Finset (Fin N))) (c : Finset (Fin N) × Fin N × Fin N),
    0 < F.cycleCount H →
    |candidateNormalizedCount (F.cycleCount H) (F.completionCount H c)
      (F.mu H) (((r:ℝ)-1)^2) - 1| ≤ alpha N/100 →
    (F.cycleCount H:ℝ)*(N:ℝ)^(-(100*(r:ℝ))) ≤ F.completionCount H c := by
  filter_upwards [eventually_tiny_polynomial_survival r (by omega) (8*(((r:ℝ)-1)^2)*r),
    eventual_range] with N hcut hR original F H c hX hnormal
  have hcut' : 8*(((r:ℝ)-1)^2)*(r*(N:ℝ)^r)*(N:ℝ)^(-(100*(r:ℝ))) ≤ 1 := by
    have he : Real.exp (-2*nu N)≤1 := Real.exp_le_one_iff.mpr (by linarith [hR.2.2.2.2.2.1])
    simpa only [Nat.cast_mul, Nat.cast_ofNat, mul_assoc] using hcut.trans he
  have hμ0 : 0 ≤ F.mu H := by unfold mu; positivity
  have hμ : 0 < F.mu H := by
    by_contra hn
    have hz : F.mu H=0 := le_antisymm (le_of_not_gt hn) hμ0
    simp only [hz, candidateNormalizedCount, mul_zero, div_zero, zero_sub, abs_neg, abs_one] at hnormal
    linarith [hR.2.2.2.2.1]
  have hrR : (3:ℝ)≤r := by exact_mod_cast hr
  have hp : 0 ≤ (N:ℝ)^(-(100*(r:ℝ))) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hbound := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (F.mu_polynomial_upper H)
      (show 0≤8*(((r:ℝ)-1)^2) by positivity)) hp
  simp only [Fintype.card_fin] at hbound
  apply normal_completion_above_cutoff _ _ _ (((r:ℝ)-1)^2) _ (alpha N/100) (by exact_mod_cast hX) hμ
    (sq_pos_of_pos (by linarith)) (by linarith [hR.2.2.2.2.1]) hnormal
  have hlarge := hbound.trans hcut'
  have hnn : 0≤(((r:ℝ)-1)^2)*F.mu H*(N:ℝ)^(-(100*(r:ℝ))) := by positivity
  nlinarith

end LooseHamilton.AuxiliaryFrame.Frame
