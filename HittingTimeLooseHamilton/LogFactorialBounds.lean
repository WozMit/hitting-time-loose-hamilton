module

public import Mathlib.Analysis.SpecialFunctions.Stirling
public import Mathlib.Tactic

public section

/-!
# Uniform logarithmic factorial estimates

This module supplies the form of Stirling's estimate used in the logarithmic
benchmark. The additive constant is absolute and the estimates include zero.
-/

namespace LooseHamilton

/-- Stirling's estimate, with an absolute additive constant and no positivity
assumption on the factorial argument. -/
theorem log_factorial_error_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ,
      |Real.log (n.factorial : ℝ) - ((n : ℝ) * Real.log n - n)| ≤
        Real.log ((n : ℝ) + 1) + C := by
  let a : ℝ := 1 - 12⁻¹ - Real.log 2 / 2
  have ha := Stirling.log_stirlingSeq_bounded_by_constant
  let b := Real.log (Stirling.stirlingSeq 1)
  refine ⟨|a| + |b| + Real.log 2, by positivity, ?_⟩
  intro n
  cases n with
  | zero => simp only [Nat.factorial_zero, Nat.cast_one, Nat.cast_zero, Real.log_one,
      Real.log_zero, zero_mul, sub_zero, abs_zero, zero_add]
            positivity
  | succ m =>
    have hn : (0 : ℝ) < (m + 1 : ℕ) := by positivity
    have hlo : a ≤ Real.log (Stirling.stirlingSeq (m + 1)) := ha m
    have hhi : Real.log (Stirling.stirlingSeq (m + 1)) ≤ b := by
      simpa [b, Function.comp_def] using
        Stirling.log_stirlingSeq'_antitone (Nat.zero_le m)
    have habs : |Real.log (Stirling.stirlingSeq (m + 1))| ≤ |a| + |b| := by
      apply abs_le.mpr
      constructor
      · have := neg_abs_le a
        have := abs_nonneg b
        linarith
      · have := le_abs_self b
        have := abs_nonneg a
        linarith
    have hlog : 0 ≤ Real.log (m + 1 : ℕ) :=
      Real.log_nonneg (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le m))
    have hlog2 : 0 ≤ Real.log (2 : ℝ) := Real.log_nonneg (by norm_num)
    have hmono : Real.log (m + 1 : ℕ) ≤ Real.log ((m + 1 : ℕ) + (1 : ℝ)) :=
      Real.log_le_log hn (by linarith)
    have hformula :
        Real.log ((m + 1).factorial : ℝ) -
          ((m + 1 : ℕ) * Real.log (m + 1 : ℕ) - (m + 1 : ℕ)) =
        Real.log (Stirling.stirlingSeq (m + 1)) +
          1 / 2 * (Real.log 2 + Real.log (m + 1 : ℕ)) := by
      have hf := Stirling.log_stirlingSeq_formula (m + 1)
      rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hn.ne',
        Real.log_div hn.ne' (Real.exp_pos 1).ne', Real.log_exp] at hf
      linarith
    rw [hformula]
    calc
      _ ≤ |Real.log (Stirling.stirlingSeq (m + 1))| +
          |1 / 2 * (Real.log 2 + Real.log (m + 1 : ℕ))| := abs_add_le _ _
      _ ≤ (|a| + |b|) + 1 / 2 * (Real.log 2 + Real.log (m + 1 : ℕ)) := by
        rw [abs_of_nonneg (show 0 ≤ (1 / 2 : ℝ) *
          (Real.log 2 + Real.log (m + 1 : ℕ)) by positivity)]
        exact add_le_add_left habs _
      _ ≤ Real.log ((m + 1 : ℕ) + (1 : ℝ)) + (|a| + |b| + Real.log 2) := by
        linarith

/-- A single constant controls every factorial argument up to an ambient size. -/
theorem log_factorial_error_bound_uniform :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N n : ℕ, n ≤ N →
      |Real.log (n.factorial : ℝ) - ((n : ℝ) * Real.log n - n)| ≤
        Real.log ((N : ℝ) + 1) + C := by
  obtain ⟨C, hC, h⟩ := log_factorial_error_bound
  refine ⟨C, hC, fun N n hn => (h n).trans ?_⟩
  apply add_le_add_left
  apply Real.log_le_log
  · positivity
  · exact_mod_cast Nat.add_le_add_right hn 1

/-- Removing a consecutive block of at most `b-a` factorial factors costs at
most `(b-a) log N` when all factors are at most `N`. -/
theorem log_factorial_gap {N a b : ℕ} (hab : a ≤ b) (hbN : b ≤ N) :
    0 ≤ Real.log (b.factorial : ℝ) - Real.log (a.factorial : ℝ) ∧
    Real.log (b.factorial : ℝ) - Real.log (a.factorial : ℝ) ≤
      ((b : ℝ) - a) * Real.log N := by
  constructor
  · exact sub_nonneg.mpr (Real.log_le_log (by positivity)
      (by exact_mod_cast Nat.factorial_le hab))
  · induction b with
    | zero => have : a = 0 := by omega
              subst a
              simp
    | succ b ih =>
      by_cases heq : a = b + 1
      · subst a
        simp
      have hab' : a ≤ b := by omega
      have hi := ih hab' (by omega)
      have hlog : Real.log (b + 1 : ℕ) ≤ Real.log N :=
        Real.log_le_log (by positivity) (by exact_mod_cast hbN)
      rw [Nat.factorial_succ, Nat.cast_mul,
        Real.log_mul (by positivity) (by positivity)]
      push_cast at hlog ⊢
      nlinarith

theorem log_factorial_gap_bound {a b N : ℕ} (hab : a ≤ b) (hbN : b ≤ N) :
    0 ≤ Real.log (b.factorial : ℝ) - Real.log (a.factorial : ℝ) ∧
    Real.log (b.factorial : ℝ) - Real.log (a.factorial : ℝ) ≤
      ((b - a : ℕ) : ℝ) * Real.log N := by
  simpa only [Nat.cast_sub hab] using log_factorial_gap hab hbN

end LooseHamilton
