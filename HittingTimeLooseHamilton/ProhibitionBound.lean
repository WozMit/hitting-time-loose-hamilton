module

public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Tactic

public section
namespace LooseHamilton
/-- The exact avoidance proportion in Proposition 2.2. -/
@[expose] noncomputable def prohibitionRatio (k s : ℕ) : ℝ :=
  ((k - s).factorial : ℝ) * ((k - s - 1).factorial : ℝ) /
    (((k - 1).factorial : ℝ) * ((k - 2 * s).factorial : ℝ))
lemma prohibitionRatio_pos (k s : ℕ) : 0 < prohibitionRatio k s := by
  unfold prohibitionRatio; positivity
lemma prohibitionRatio_one {k : ℕ} (hk : 2 ≤ k) : prohibitionRatio k 1 = 1 := by
  unfold prohibitionRatio
  have h : k - 1 - 1 = k - 2 * 1 := by omega
  rw [h]
  have h₁ : (0 : ℝ) < ((k - 1).factorial : ℝ) := by positivity
  have h₂ : (0 : ℝ) < ((k - 2 * 1).factorial : ℝ) := by positivity
  field_simp
lemma prohibitionRatio_step {k s : ℕ} (hs : 1 ≤ s) (hk : 2 * (s + 1) ≤ k) :
    prohibitionRatio k (s + 1) = prohibitionRatio k s *
      (((k : ℝ) - 2 * s) * (k - 2 * s - 1) /
        (((k : ℝ) - s) * (k - s - 1))) := by
  have h₁ : k - s = (k - (s + 1)) + 1 := by omega
  have h₂ : k - s - 1 = (k - (s + 1) - 1) + 1 := by omega
  have h₃ : k - 2 * s = (k - 2 * (s + 1)) + 1 + 1 := by omega
  have hc₁ : ((k - (s + 1) + 1 : ℕ) : ℝ) = (k : ℝ) - s := by
    rw [← h₁, Nat.cast_sub (by omega)]
  have hc₂ : ((k - (s + 1) - 1 + 1 : ℕ) : ℝ) = (k : ℝ) - s - 1 := by
    rw [← h₂, Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; norm_num
  have hc₃ : ((k - 2 * (s + 1) + 1 + 1 : ℕ) : ℝ) = (k : ℝ) - 2 * s := by
    rw [← h₃, Nat.cast_sub (by omega)]; push_cast; ring
  have hc₄ : ((k - 2 * (s + 1) + 1 : ℕ) : ℝ) = (k : ℝ) - 2 * s - 1 := by
    have : k - 2 * (s + 1) + 1 = k - 2 * s - 1 := by omega
    rw [this, Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; push_cast; ring
  have hf₁ : ((k - s).factorial : ℝ) = ((k : ℝ) - s) * ((k - (s + 1)).factorial : ℝ) := by
    conv_lhs => rw [h₁, Nat.factorial_succ, Nat.cast_mul]
    rw [hc₁]
  have hf₂ : ((k - s - 1).factorial : ℝ) = ((k : ℝ) - s - 1) * ((k - (s + 1) - 1).factorial : ℝ) := by
    conv_lhs => rw [h₂, Nat.factorial_succ, Nat.cast_mul]
    rw [hc₂]
  have hf₃ : ((k - 2 * s).factorial : ℝ) = ((k : ℝ) - 2 * s) * (k - 2 * s - 1) * ((k - 2 * (s + 1)).factorial : ℝ) := by
    conv_lhs => rw [h₃, Nat.factorial_succ, Nat.factorial_succ, Nat.cast_mul, Nat.cast_mul]
    rw [hc₃, hc₄]
    ring
  unfold prohibitionRatio
  rw [hf₁, hf₂, hf₃]
  have hks : (k : ℝ) - s > 0 := by
    have : (s : ℝ) < k := by exact_mod_cast (show s < k by omega)
    linarith
  have hks' : (k : ℝ) - s - 1 > 0 := by
    have : (s : ℝ) + 1 < k := by exact_mod_cast (show s + 1 < k by omega)
    linarith
  have hf : ((k - 2 * (s + 1)).factorial : ℝ) ≠ 0 := by positivity
  have hg : ((k - 1).factorial : ℝ) ≠ 0 := by positivity
  have ht : (k : ℝ) - 2 * s > 1 := by
    have : 2 * ((s : ℝ) + 1) ≤ k := by exact_mod_cast hk
    linarith
  have ht₁ : 0 < (k : ℝ) - 2 * s := by linarith
  have ht₂ : 0 < (k : ℝ) - 2 * s - 1 := by linarith
  rw [div_mul_div_comm]
  apply (div_eq_div_iff (by positivity) (by positivity)).2
  ring

private lemma step_lower {x t : ℝ} (ht : 1 ≤ t) (hx : 2 * (t + 1) ≤ x) :
    1 - (t + 1) * t / (x - 1) ≤
      (1 - t * (t - 1) / (x - 1)) *
        ((x - 2 * t) * (x - 2 * t - 1) / ((x - t) * (x - t - 1))) := by
  have h₁ : 0 < x - 1 := by linarith
  have h₂ : 0 < x - t := by linarith
  have h₃ : 0 < x - t - 1 := by linarith
  have he : 0 ≤ (2 * t - 1) * (x - 2 * (t + 1)) :=
    mul_nonneg (by linarith) (by linarith)
  have hb : 0 ≤ (2 * t - 1) * x - 3 * t ^ 2 + t + 1 := by
    nlinarith [sq_nonneg t]
  have hp := mul_nonneg (mul_nonneg (show 0 ≤ t by linarith)
    (show 0 ≤ t - 1 by linarith)) hb
  rw [← mul_div_assoc]
  apply (le_div_iff₀ (mul_pos h₂ h₃)).2
  have ha (a : ℝ) : 1 - a / (x - 1) = (x - 1 - a) / (x - 1) := by
    rw [sub_div, div_self h₁.ne']
  rw [ha, ha, div_mul_eq_mul_div, div_mul_eq_mul_div]
  apply (div_le_div_iff_of_pos_right h₁).2
  nlinarith

/-- The explicit lower bound in Proposition 2.2. -/
theorem prohibitionRatio_lower {k s : ℕ} (hs : 1 ≤ s) (hk : 2 * s ≤ k) :
    1 - (s : ℝ) * (s - 1) / (k - 1) ≤ prohibitionRatio k s := by
  induction s, hs using Nat.le_induction with
  | base => rw [prohibitionRatio_one (k := k) (by omega)]; norm_num
  | succ s hs ih =>
    have ih' := ih (by omega)
    rw [prohibitionRatio_step hs hk]
    have hsR : (1 : ℝ) ≤ s := by exact_mod_cast hs
    have hkR : 2 * ((s : ℝ) + 1) ≤ k := by exact_mod_cast hk
    have hfac : 0 ≤ ((k : ℝ) - 2 * s) * (k - 2 * s - 1) /
        (((k : ℝ) - s) * (k - s - 1)) := by
      apply div_nonneg <;> apply mul_nonneg <;> linarith
    calc
      _ ≤ (1 - (s : ℝ) * (s - 1) / (k - 1)) *
          (((k : ℝ) - 2 * s) * (k - 2 * s - 1) /
            (((k : ℝ) - s) * (k - s - 1))) := by
        push_cast
        convert step_lower hsR hkR using 1
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_right ih' hfac

/-- The avoidance proportion is at most one in the admissible range. -/
theorem prohibitionRatio_le_one {k s : ℕ} (hs : 1 ≤ s) (hk : 2 * s ≤ k) :
    prohibitionRatio k s ≤ 1 := by
  induction s, hs using Nat.le_induction with
  | base => rw [prohibitionRatio_one (k := k) (by omega)]
  | succ s hs ih =>
    have ih' := ih (by omega)
    rw [prohibitionRatio_step hs hk]
    have hsR : (1 : ℝ) ≤ s := by exact_mod_cast hs
    have hkR : 2 * ((s : ℝ) + 1) ≤ k := by exact_mod_cast hk
    have h₁ : 0 ≤ (k : ℝ) - 2 * s := by linarith
    have h₂ : 0 ≤ (k : ℝ) - 2 * s - 1 := by linarith
    have h₃ : 0 < (k : ℝ) - s := by linarith
    have h₄ : 0 < (k : ℝ) - s - 1 := by linarith
    have hfac : 0 ≤ ((k : ℝ) - 2 * s) * (k - 2 * s - 1) /
        (((k : ℝ) - s) * (k - s - 1)) :=
      div_nonneg (mul_nonneg h₁ h₂) (le_of_lt (mul_pos h₃ h₄))
    have hfac' : ((k : ℝ) - 2 * s) * (k - 2 * s - 1) /
        (((k : ℝ) - s) * (k - s - 1)) ≤ 1 := by
      apply (div_le_one (mul_pos h₃ h₄)).2
      apply mul_le_mul (by linarith) (by linarith) h₂ (le_of_lt h₃)
    exact (mul_le_mul_of_nonneg_right ih' hfac).trans (by simpa using hfac')
end LooseHamilton

