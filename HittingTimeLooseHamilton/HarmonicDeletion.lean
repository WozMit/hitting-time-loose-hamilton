module

public import Mathlib.NumberTheory.Harmonic.EulerMascheroni
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Tactic

public section

/-! A finite, uniform estimate for the harmonic deletion baseline. -/

namespace LooseHamilton

/-- The harmonic sum over the deletion interval. -/
@[expose] noncomputable def deletionHarmonic (j K : ℕ) : ℝ :=
  ∑ h ∈ Finset.Ioc j K, (h : ℝ)⁻¹

lemma deletionHarmonic_eq_harmonic_sub {j K : ℕ} (hjK : j ≤ K) :
    deletionHarmonic j K = (harmonic K : ℝ) - harmonic j := by
  induction K, hjK using Nat.le_induction with
  | base => simp [deletionHarmonic]
  | succ K hjK ih =>
    rw [deletionHarmonic, Finset.sum_Ioc_succ_top hjK]
    change deletionHarmonic j K + ((K + 1 : ℕ) : ℝ)⁻¹ = _
    rw [ih, harmonic_succ]
    push_cast
    ring

/-- The deletion harmonic sum approximates `log (K/j)`, with error at most `1/j`.
The bound is independent of the upper endpoint. -/
theorem deletionHarmonic_log_bound {j K : ℕ} (hj : 1 ≤ j) (hjK : j ≤ K) :
    |deletionHarmonic j K - Real.log ((K : ℝ) / j)| ≤ (j : ℝ)⁻¹ := by
  have hj0 : j ≠ 0 := by omega
  have hK0 : K ≠ 0 := by omega
  have hjpos : (0 : ℝ) < j := by exact_mod_cast (show 0 < j by omega)
  have hKpos : (0 : ℝ) < K := by exact_mod_cast (show 0 < K by omega)
  have hu := Real.strictAnti_eulerMascheroniSeq'.antitone hjK
  simp only [Real.eulerMascheroniSeq', if_neg hj0, if_neg hK0] at hu
  have hl := Real.strictMono_eulerMascheroniSeq.monotone hjK
  simp only [Real.eulerMascheroniSeq] at hl
  have hlog : Real.log (K : ℝ) ≤ Real.log ((K : ℝ) + 1) :=
    Real.log_le_log hKpos (by linarith)
  have hstep : Real.log ((j : ℝ) + 1) - Real.log (j : ℝ) ≤ (j : ℝ)⁻¹ := by
    rw [← Real.log_div (by positivity) (ne_of_gt hjpos)]
    have h := Real.log_le_sub_one_of_pos (show 0 < ((j : ℝ) + 1) / j by positivity)
    have heq : ((j : ℝ) + 1) / j - 1 = (j : ℝ)⁻¹ := by field_simp <;> ring
    rwa [heq] at h
  rw [deletionHarmonic_eq_harmonic_sub hjK,
    Real.log_div (ne_of_gt hKpos) (ne_of_gt hjpos), abs_le]
  constructor <;> linarith [inv_pos.mpr hjpos]

/-- Multiplying the deletion baseline by the number of ordinary edges preserves
its explicit error estimate. -/
theorem scaled_deletionHarmonic_log_bound {j K : ℕ} (k : ℕ)
    (hj : 1 ≤ j) (hjK : j ≤ K) :
    |(k : ℝ) * deletionHarmonic j K - (k : ℝ) * Real.log ((K : ℝ) / j)| ≤
      (k : ℝ) / j := by
  rw [← mul_sub, abs_mul, abs_of_nonneg (Nat.cast_nonneg k), div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_left (deletionHarmonic_log_bound hj hjK) (Nat.cast_nonneg k)

end LooseHamilton
