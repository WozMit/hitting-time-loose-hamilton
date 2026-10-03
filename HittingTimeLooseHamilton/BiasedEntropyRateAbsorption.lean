module

public import HittingTimeLooseHamilton.BiasedEntropyRates

public section

noncomputable section
namespace FiniteEntropy

/-- Absorb the collision entropy rate into a common power-plus-inverse-log
budget. X,Y stand for the two nonnegative target rate components. -/
theorem collision_rate_absorption {A N n r K X Y Z W : ℝ}
    (hA : 0 ≤ A) (hN : 0 ≤ N) ( _hn : 0 ≤ n) (hr : 0 ≤ r) (hK : 0 ≤ K)
    (hX : 0 ≤ X) (hY : 0 ≤ Y) (hZ : 0 ≤ Z) (hW : 0 ≤ W)
    (hsize : n ≤ r*N) (hpower : Z ≤ K*X) (hlog : W ≤ 2*Y) :
    n*Z + 2*(A*N+n*Real.log 2)*W ≤
      (r*K+4*(A+r*Real.log 2))*N*(X+Y) := by
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hfirst : n*Z ≤ r*K*N*X := by
    calc
      _ ≤ (r*N)*(K*X) := mul_le_mul hsize hpower hZ (by positivity)
      _ = _ := by ring
  have hsecond : 2*(A*N+n*Real.log 2)*W ≤ 4*(A+r*Real.log 2)*N*Y := by
    calc
      _ ≤ 2*(A*N+(r*N)*Real.log 2)*(2*Y) := by gcongr
      _ = _ := by ring
  have hcross1 : 0 ≤ r*K*N*Y := by positivity
  have hcross2 : 0 ≤ 4*(A+r*Real.log 2)*N*X := by positivity
  nlinarith only [hfirst,hsecond,hcross1,hcross2]

/-- A logarithmic counting error is a constant multiple of log N once N≥2.
The coefficient is universal and deliberately explicit. -/
theorem log_succ_add_one_le_log {N : ℝ} (hN : 2 ≤ N) :
    Real.log (N+1)+1 ≤ (2+1/Real.log 2)*Real.log N := by
  have hNp : 0 < N := by linarith
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlN : Real.log 2 ≤ Real.log N := Real.log_le_log (by norm_num) hN
  have hsucc : Real.log (N+1) ≤ Real.log 2+Real.log N := by
    have h := Real.log_le_log (show 0 < N+1 by linarith) (show N+1 ≤ 2*N by linarith)
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hNp.ne'] at h
    exact h
  have hratio : 1 ≤ Real.log N / Real.log 2 := (le_div_iff₀ hl2).2 (by linarith)
  have heq : (2+1/Real.log 2)*Real.log N = 2*Real.log N+Real.log N/Real.log 2 := by ring
  rw [heq]
  linarith

/-- Changing from log N to log(r*k) costs only a fixed-uniformity factor when
k≤N and the logarithm is evaluated on a positive product. -/
theorem log_uniformity_size_le {r k N : ℝ} (hr : 1 ≤ r) (hk : 0 < k)
    (hN : 2 ≤ N) (hkN : k ≤ N) :
    Real.log (r*k) ≤ (1+Real.log r/Real.log 2)*Real.log N := by
  have hrp : 0 < r := by linarith
  have hNp : 0 < N := by linarith
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlN : Real.log 2 ≤ Real.log N := Real.log_le_log (by norm_num) hN
  have hlr : 0 ≤ Real.log r := Real.log_nonneg hr
  have hratio : 1 ≤ Real.log N/Real.log 2 := (le_div_iff₀ hl2).2 (by linarith)
  have h := mul_le_mul_of_nonneg_left hratio hlr
  have hklog := Real.log_le_log hk hkN
  rw [Real.log_mul hrp.ne' hk.ne']
  have heq : (1+Real.log r/Real.log 2)*Real.log N =
      Real.log N+Real.log r*(Real.log N/Real.log 2) := by ring
  rw [heq]
  linarith

end FiniteEntropy
