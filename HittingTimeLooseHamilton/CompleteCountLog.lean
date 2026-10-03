module

public import HittingTimeLooseHamilton.NormalizationFactorials
public import HittingTimeLooseHamilton.ProhibitionBound
public import HittingTimeLooseHamilton.LogFactorialBounds

public section

set_option maxHeartbeats 2000000

noncomputable section
namespace LooseHamilton

/-- Cancellation of the forbidden-port proportion in the complete-host count. -/
theorem allowedCompleteFormula {r N k s : ℕ}
    (hr : 3 ≤ r) (hsk : s ≤ k) (hN : N = (r-1)*k+s) :
    (completeHostFormula r N k s : ℝ) * prohibitionRatio k s =
      (2:ℝ)^(s-1) * (N-2*s).factorial * (k-s-1).factorial /
        ((k-2*s).factorial * ((r-2).factorial:ℝ)^k) := by
  rw [completeHostFormula_cast hr hsk hN]
  unfold prohibitionRatio
  have hf (n : ℕ) : (n.factorial : ℝ) ≠ 0 := by positivity
  field_simp [hf, pow_ne_zero] <;> ring

/-- Exact logarithmic form of the allowed complete-host enumeration. -/
theorem log_allowedCompleteFormula {r N k s : ℕ}
    (hr : 3 ≤ r) (hsk : s ≤ k) (hN : N = (r-1)*k+s) :
    Real.log ((completeHostFormula r N k s : ℝ) * prohibitionRatio k s) =
      ((s-1 : ℕ) : ℝ) * Real.log 2 + Real.log ((N-2*s).factorial : ℝ) +
        Real.log ((k-s-1).factorial : ℝ) - Real.log ((k-2*s).factorial : ℝ) -
          (k:ℝ) * Real.log ((r-2).factorial : ℝ) := by
  rw [allowedCompleteFormula hr hsk hN,
    Real.log_div (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow]
  ring

/-- Uniform coarse logarithmic estimate; its constant is absolute. -/
theorem log_allowedCompleteFormula_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r N k s : ℕ,
      3 ≤ r → 2 ≤ N → 1 ≤ s → 2*s ≤ k → N = (r-1)*k+s →
      |Real.log ((completeHostFormula r N k s : ℝ) * prohibitionRatio k s) -
        (((N:ℝ)-s)*Real.log N - ((N:ℝ)-s) -
          (k:ℝ)*Real.log ((r-2).factorial:ℝ))| ≤
        C*((s:ℝ)+1)*(Real.log N+1) := by
  obtain ⟨C, hC, hfac⟩ := log_factorial_error_bound_uniform
  refine ⟨C+10, by linarith, ?_⟩
  intro r N k s hr hN2 hs hsk hN
  have hkN : k ≤ N := by
    have hr1 : 1 ≤ r-1 := by omega
    have hh : k ≤ (r-1)*k := by simpa using Nat.mul_le_mul_right k hr1
    omega
  have h2sN : 2*s ≤ N := by omega
  have hlog : 0 ≤ Real.log (N:ℝ) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ N by omega))
  have hsR : (0:ℝ) ≤ s := by positivity
  have hNpos : (0:ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hlog2 : Real.log (2:ℝ) ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
    norm_num at this ⊢
    exact this
  have hlog2pos : 0 ≤ Real.log (2:ℝ) := Real.log_nonneg (by norm_num)
  have hlogadd : Real.log ((N:ℝ)+1) ≤ Real.log (N:ℝ)+1 := by
    calc
      _ ≤ Real.log (2*(N:ℝ)) := Real.log_le_log (by positivity) (by
        have : (1:ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
        linarith)
      _ = Real.log 2 + Real.log (N:ℝ) := Real.log_mul (by norm_num) hNpos.ne'
      _ ≤ _ := by linarith
  have herr := hfac N N le_rfl
  have herr' : |Real.log (N.factorial:ℝ)-((N:ℝ)*Real.log N-N)| ≤
      Real.log (N:ℝ)+1+C := herr.trans (by linarith)
  have hgapN := log_factorial_gap (show N-2*s ≤ N by omega) (show N ≤ N from le_rfl)
  have hgapk := log_factorial_gap (N := N)
    (show k-2*s ≤ k-s-1 by omega) (show k-s-1 ≤ N by omega)
  have hlenN : (N:ℝ)-((N-2*s:ℕ):ℝ) = 2*(s:ℝ) := by
    rw [Nat.cast_sub h2sN]
    push_cast
    ring
  rw [hlenN] at hgapN
  have hlenk : ((k-s-1:ℕ):ℝ)-((k-2*s:ℕ):ℝ) ≤ (s:ℝ) := by
    have : ((k-s-1:ℕ):ℝ) ≤ ((k-2*s:ℕ):ℝ)+(s:ℝ) := by
      exact_mod_cast (show k-s-1 ≤ (k-2*s)+s by omega)
    linarith
  have hgapk' : Real.log ((k-s-1).factorial:ℝ)-Real.log ((k-2*s).factorial:ℝ) ≤
      (s:ℝ)*Real.log N := hgapk.2.trans (mul_le_mul_of_nonneg_right hlenk hlog)
  have hmlo : 0 ≤ ((s-1:ℕ):ℝ)*Real.log 2 := mul_nonneg (by positivity) hlog2pos
  have hmhi : ((s-1:ℕ):ℝ)*Real.log 2 ≤ (s:ℝ) := by
    calc
      _ ≤ ((s-1:ℕ):ℝ)*1 := mul_le_mul_of_nonneg_left hlog2 (by positivity)
      _ ≤ _ := by simp only [mul_one]; exact_mod_cast Nat.sub_le s 1
  rw [log_allowedCompleteFormula hr (by omega) hN]
  obtain ⟨he1, he2⟩ := abs_le.mp herr'
  have hsl : 0 ≤ (s:ℝ)*Real.log N := mul_nonneg hsR hlog
  have hCl : 0 ≤ C*Real.log N := mul_nonneg hC hlog
  have hCs : 0 ≤ C*(s:ℝ) := mul_nonneg hC hsR
  have hCsl : 0 ≤ C*((s:ℝ)*Real.log N) := mul_nonneg hC hsl
  apply abs_le.mpr
  constructor <;> nlinarith [hgapN.1, hgapN.2, hgapk.1]

end LooseHamilton
