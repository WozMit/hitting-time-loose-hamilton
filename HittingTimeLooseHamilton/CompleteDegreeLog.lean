module

public import HittingTimeLooseHamilton.NormalizationFormula
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Tactic

public section

/-! # A quantitative logarithmic estimate for the complete-host degree -/
noncomputable section
namespace LooseHamilton

private lemma log_sub_error (x a : ℝ) (ha : 0 ≤ a) (hxa : 2 * a < x) :
    0 ≤ Real.log x - Real.log (x - a) ∧
      Real.log x - Real.log (x - a) ≤ 2 * a / x := by
  have hx : 0 < x := by linarith
  have hy : 0 < x - a := by linarith
  constructor
  · exact sub_nonneg.mpr (Real.log_le_log hy (by linarith))
  · rw [← Real.log_div hx.ne' hy.ne']
    calc
      Real.log (x / (x - a)) ≤ x / (x - a) - 1 :=
        Real.log_le_sub_one_of_pos (div_pos hx hy)
      _ = a / (x - a) := by field_simp <;> ring
      _ ≤ 2 * a / x := by
        apply (div_le_div_iff₀ hy hx).mpr
        nlinarith

/-- A fixed-length descending factorial differs logarithmically from a power
by at most a constant divided by the ambient size. -/
theorem log_descFactorial_error {N m : ℕ} (hN : 2 * m < N) :
    |Real.log (((N - 1).descFactorial m : ℕ) : ℝ) -
      (m : ℝ) * Real.log N| ≤ 2 * (m : ℝ)^2 / N := by
  have hmN : m < N := by omega
  have hN1 : 1 ≤ N := by omega
  have hsub : N - 1 + 1 - m = N - m := by omega
  have hlow : (N - m)^m ≤ (N - 1).descFactorial m := by
    simpa [hsub] using Nat.pow_sub_le_descFactorial (N - 1) m
  have hupp : (N - 1).descFactorial m ≤ N^m :=
    (Nat.descFactorial_le_pow _ _).trans (Nat.pow_le_pow_left (by omega) _)
  have hx : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hy : (0 : ℝ) < (N : ℝ) - m := by
    have : (m : ℝ) < N := by exact_mod_cast hmN
    linarith
  have hcast : ((N - m : ℕ) : ℝ) = (N : ℝ) - m := Nat.cast_sub (by omega)
  have hlo : ((N : ℝ) - m)^m ≤ (((N - 1).descFactorial m : ℕ) : ℝ) := by
    rw [← hcast]
    exact_mod_cast hlow
  have hup : (((N - 1).descFactorial m : ℕ) : ℝ) ≤ (N : ℝ)^m := by exact_mod_cast hupp
  have hdpos : (0 : ℝ) < (((N - 1).descFactorial m : ℕ) : ℝ) :=
    lt_of_lt_of_le (pow_pos hy _) hlo
  have hl := Real.log_le_log (pow_pos hy m) hlo
  have hu := Real.log_le_log hdpos hup
  rw [Real.log_pow] at hl hu
  have he := (log_sub_error (N : ℝ) m (Nat.cast_nonneg _) (by exact_mod_cast hN)).2
  rw [abs_of_nonpos (by linarith : Real.log (((N - 1).descFactorial m : ℕ) : ℝ) -
      (m : ℝ) * Real.log N ≤ 0)]
  have hmul := mul_le_mul_of_nonneg_left he (Nat.cast_nonneg m : (0 : ℝ) ≤ m)
  calc
    -(Real.log (((N - 1).descFactorial m : ℕ) : ℝ) - (m : ℝ) * Real.log N)
      ≤ (m : ℝ) * (Real.log N - Real.log ((N : ℝ) - m)) := by nlinarith
    _ ≤ (m : ℝ) * (2 * m / N) := hmul
    _ = 2 * (m : ℝ)^2 / N := by ring

/-- The complete-degree term in the benchmark has a bounded total error. -/
theorem completeMeanDegree_log_error {r N k : ℕ}
    (hr : 3 ≤ r) (hN : 2 * r ≤ N) (hk : k ≤ N) :
    (k : ℝ) * |Real.log (((r : ℝ) - 1) * completeMeanDegree r N) -
      (((r : ℝ) - 1) * Real.log N - Real.log ((r - 2).factorial : ℝ))|
      ≤ 2 * (r : ℝ)^2 := by
  have hm : r - 1 + 1 = r := by omega
  have hm2 : r - 2 + 1 = r - 1 := by omega
  have hc : ((r - 1 : ℕ) : ℝ) = (r : ℝ) - 1 := by
    rw [Nat.cast_sub (show 1 ≤ r by omega), Nat.cast_one]
  have hf : (((r - 1).factorial : ℕ) : ℝ) =
      ((r : ℝ) - 1) * ((r - 2).factorial : ℝ) := by
    rw [← hc]
    exact_mod_cast (show (r - 1).factorial = (r - 1) * (r - 2).factorial by
      conv_lhs => rw [← hm2, Nat.factorial_succ]
      rw [hm2])
  have heq : (((r : ℝ) - 1) * completeMeanDegree r N) =
      (((N - 1).descFactorial (r - 1) : ℕ) : ℝ) / ((r - 2).factorial : ℝ) := by
    rw [Nat.descFactorial_eq_factorial_mul_choose, Nat.cast_mul, hf]
    unfold completeMeanDegree
    field_simp <;> ring
  have hpos : (0 : ℝ) < (((N - 1).descFactorial (r - 1) : ℕ) : ℝ) := by
    have hd : 0 < (N - 1).descFactorial (r - 1) := by
      apply Nat.pos_of_ne_zero
      intro hz
      have := Nat.descFactorial_eq_zero_iff_lt.mp hz
      omega
    exact_mod_cast hd
  have hfact : (0 : ℝ) < ((r - 2).factorial : ℝ) := by positivity
  rw [heq, Real.log_div hpos.ne' hfact.ne']
  have he := log_descFactorial_error (N := N) (m := r - 1) (by omega)
  rw [hc] at he
  have hkn : (k : ℝ) ≤ N := by exact_mod_cast hk
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  calc
    (k : ℝ) * |Real.log (((N - 1).descFactorial (r - 1) : ℕ) : ℝ) -
        Real.log ((r - 2).factorial : ℝ) -
        (((r : ℝ) - 1) * Real.log N - Real.log ((r - 2).factorial : ℝ))|
      = (k : ℝ) * |Real.log (((N - 1).descFactorial (r - 1) : ℕ) : ℝ) -
        ((r : ℝ) - 1) * Real.log N| := by congr 2; ring
    _ ≤ (k : ℝ) * (2 * ((r : ℝ) - 1)^2 / N) :=
      mul_le_mul_of_nonneg_left he (Nat.cast_nonneg _)
    _ ≤ (N : ℝ) * (2 * ((r : ℝ) - 1)^2 / N) :=
      mul_le_mul_of_nonneg_right hkn (by positivity)
    _ = 2 * ((r : ℝ) - 1)^2 := by field_simp <;> ring
    _ ≤ 2 * (r : ℝ)^2 := by
      have : (3 : ℝ) ≤ r := by exact_mod_cast hr
      nlinarith
end LooseHamilton
