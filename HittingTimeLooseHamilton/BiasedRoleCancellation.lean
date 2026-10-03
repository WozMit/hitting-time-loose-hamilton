module

public import HittingTimeLooseHamilton.LogFactorialBounds
public import Mathlib.Analysis.SpecialFunctions.BinaryEntropy

public section

/-! Scalar entropy identities used in the biased-role argument. -/
noncomputable section
namespace LooseHamilton

/-- The binary junction entropy cancels the private-slot density exactly. -/
theorem biased_role_entropy_cancellation_real {t : ℝ} (ht : 1 < t) :
    t * Real.binEntropy (1 / t) + (t - 1) * Real.log ((t - 1) / t) =
      Real.log t := by
  have ht0 : t ≠ 0 := by linarith
  have hb : 1 - 1 / t = (t - 1) / t := by field_simp <;> ring
  simp only [Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub, Real.negMulLog_def]
  rw [hb]
  simp only [one_div, inv_inv, Real.log_inv]
  field_simp <;> ring

/-- The identity printed after the role-support estimate in Theorem 6.1. -/
theorem biased_role_entropy_cancellation (r : ℕ) (hr : 3 ≤ r) :
    ((r : ℝ) - 1) * Real.binEntropy (1 / ((r : ℝ) - 1)) +
      ((r : ℝ) - 2) * Real.log (((r : ℝ) - 2) / ((r : ℝ) - 1)) =
      Real.log ((r : ℝ) - 1) := by
  have h := biased_role_entropy_cancellation_real (t := (r : ℝ) - 1)
    (by
      have : (3 : ℝ) ≤ r := by exact_mod_cast hr
      linarith)
  have hsub : (r : ℝ) - 1 - 1 = (r : ℝ) - 2 := by ring
  simpa only [hsub] using h

/-- Exact entropy algebra for a positive split of a finite set. -/
theorem scaled_binary_entropy {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    (x + y) * Real.binEntropy (x / (x + y)) =
      (x + y) * Real.log (x + y) - x * Real.log x - y * Real.log y := by
  have hs : x + y ≠ 0 := by positivity
  have hc : 1 - x / (x + y) = y / (x + y) := by field_simp <;> ring
  simp only [Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub, Real.negMulLog_def]
  rw [hc]
  rw [Real.log_div hx.ne' hs, Real.log_div hy.ne' hs]
  field_simp <;> ring

/-- Uniform logarithmic error in the fixed-weight role support. -/
theorem log_choose_binary_entropy_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ L j : ℕ, 0 < j → j < L →
      |Real.log (L.choose j : ℝ) -
        (L : ℝ) * Real.binEntropy ((j : ℝ) / L)| ≤
          3 * Real.log ((L : ℝ) + 1) + C := by
  obtain ⟨C, hC, hfac⟩ := log_factorial_error_bound_uniform
  refine ⟨3 * C, by positivity, ?_⟩
  intro L j hj hjL
  have hjle : j ≤ L := hjL.le
  have hd : 0 < L-j := Nat.sub_pos_of_lt hjL
  have heq : (j : ℝ) + (L-j : ℕ) = L := by
    rw [Nat.cast_sub hjle]; ring
  have hsplit := scaled_binary_entropy (x := (j : ℝ)) (y := (L-j : ℕ))
    (by exact_mod_cast hj) (by exact_mod_cast hd)
  rw [heq] at hsplit
  have hnat := Nat.choose_mul_factorial_mul_factorial hjle
  have hreal : (L.choose j : ℝ) * j.factorial * (L-j).factorial = L.factorial := by
    exact_mod_cast hnat
  have hc : (L.choose j : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos hjle).ne'
  have hjf : (j.factorial : ℝ) ≠ 0 := by positivity
  have hdf : ((L-j).factorial : ℝ) ≠ 0 := by positivity
  have hlog := congrArg Real.log hreal
  rw [Real.log_mul (mul_ne_zero hc hjf) hdf, Real.log_mul hc hjf] at hlog
  have h1 := abs_le.mp (hfac L L le_rfl)
  have h2 := abs_le.mp (hfac L j hjle)
  have h3 := abs_le.mp (hfac L (L-j) (Nat.sub_le _ _))
  apply abs_le.mpr
  constructor <;> linarith

/-- Bernoulli relative entropy is at most its quadratic chi-square bound. -/
theorem bernoulli_cross_entropy_gap_le {a q : ℝ}
    (ha : 0 < a) (ha1 : a < 1) (hq : 0 < q) (hq1 : q < 1) :
    -q * Real.log a - (1-q) * Real.log (1-a) - Real.binEntropy q ≤
      (q-a)^2 / (a*(1-a)) := by
  have hb : 0 < 1-a := by linarith
  have hc : 0 < 1-q := by linarith
  have h1 := mul_le_mul_of_nonneg_left
    (Real.log_le_sub_one_of_pos (div_pos hq ha)) hq.le
  have h2 := mul_le_mul_of_nonneg_left
    (Real.log_le_sub_one_of_pos (div_pos hc hb)) hc.le
  rw [Real.log_div hq.ne' ha.ne'] at h1
  rw [Real.log_div hc.ne' hb.ne'] at h2
  have hid : q*(q/a-1) + (1-q)*((1-q)/(1-a)-1) =
      (q-a)^2/(a*(1-a)) := by
    field_simp <;> ring
  simp only [Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub, Real.negMulLog_def]
  linarith

/-- Fixed-weight Bernoulli cross entropy differs from log support by at most
its quadratic displacement plus a logarithmic counting error. -/
theorem fixed_weight_cross_entropy_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ L j : ℕ, 0 < j → j < L →
      ∀ a : ℝ, 0 < a → a < 1 →
      -(j : ℝ)*Real.log a - ((L : ℝ)-j)*Real.log (1-a) -
          Real.log (L.choose j : ℝ) ≤
        (L : ℝ) * (((j : ℝ)/L-a)^2/(a*(1-a))) +
          3*Real.log ((L : ℝ)+1)+C := by
  obtain ⟨C, hC, hchoose⟩ := log_choose_binary_entropy_bound
  refine ⟨C, hC, ?_⟩
  intro L j hj hjL a ha ha1
  have hL : (0 : ℝ) < L := by exact_mod_cast (lt_trans hj hjL)
  have hjr : (0 : ℝ) < j := by exact_mod_cast hj
  have hjLr : (j : ℝ) < L := by exact_mod_cast hjL
  have hgap := mul_le_mul_of_nonneg_left
    (bernoulli_cross_entropy_gap_le ha ha1 (div_pos hjr hL)
      ((div_lt_one hL).mpr hjLr)) hL.le
  have heq : (L : ℝ)*(-(j : ℝ)/L*Real.log a -
      (1-(j : ℝ)/L)*Real.log (1-a)-Real.binEntropy ((j : ℝ)/L)) =
      -(j : ℝ)*Real.log a - ((L : ℝ)-j)*Real.log (1-a) -
        (L : ℝ)*Real.binEntropy ((j : ℝ)/L) := by
    field_simp <;> ring
  have hc := (abs_le.mp (hchoose L j hj hjL)).1
  have hn : -((j : ℝ)/L) = -(j : ℝ)/L := by ring
  rw [hn, heq] at hgap
  linarith

/-- Under the cycle vertex identity the quadratic displacement has exact size
`(r-2)s²/(N-2s)`, explaining the marker error in biased role balance. -/
theorem role_weight_quadratic_identity {r N k s : ℝ}
    (hr : 2 < r) (hL : 0 < N-2*s) (hbook : N = (r-1)*k+s) :
    (N-2*s) * (((k-s)/(N-2*s)-1/(r-1))^2 /
      ((1/(r-1))*(1-1/(r-1)))) = (r-2)*s^2/(N-2*s) := by
  have hr1 : r-1 ≠ 0 := by linarith
  have hr2 : r-2 ≠ 0 := by linarith
  have hratio : 1-1/(r-1) = (r-2)/(r-1) := by
    field_simp <;> ring
  rw [hratio]
  field_simp <;> ring
  rw [hbook]
  ring

end LooseHamilton
