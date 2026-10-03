module

public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Data.Real.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.NormNum

public section

/-! Comparison between sampling without replacement and the power kernel in (39). -/
namespace Kahn

/-- Cross-multiplied falling-factorial comparison, including zero numerators. -/
lemma descFactorial_mul_pow_le {t m : ℕ} (ht : 1 ≤ t) (htm : t ≤ m) (d : ℕ) :
    (t - 1).descFactorial d * m ^ d ≤ (m - 1).descFactorial d * t ^ d := by
  induction d with
  | zero => simp
  | succ d ih =>
    by_cases hsmall : t ≤ d + 1
    · have hz : (t - 1).descFactorial (d + 1) = 0 :=
        Nat.descFactorial_eq_zero_iff_lt.mpr (by omega)
      rw [hz, zero_mul]
      exact Nat.zero_le _
    · have ht' : (t - 1 - d) + (d + 1) = t := by omega
      have hm' : (m - 1 - d) + (d + 1) = m := by omega
      have hmul : (d + 1) * t ≤ (d + 1) * m := Nat.mul_le_mul_left _ htm
      have hf : (t - 1 - d) * m ≤ (m - 1 - d) * t := by nlinarith
      calc
        (t - 1).descFactorial (d + 1) * m ^ (d + 1) =
            ((t - 1).descFactorial d * m ^ d) * ((t - 1 - d) * m) := by
              rw [Nat.descFactorial_succ, pow_succ]
              ring
        _ ≤ ((m - 1).descFactorial d * t ^ d) * ((m - 1 - d) * t) :=
          Nat.mul_le_mul ih hf
        _ = (m - 1).descFactorial (d + 1) * t ^ (d + 1) := by
          rw [Nat.descFactorial_succ, pow_succ]
          ring

/-- The finite sampling kernel in (36) is at most the power kernel used in (39). -/
lemma descFactorial_ratio_le_pow {t m d : ℕ} (ht : 1 ≤ t) (htm : t ≤ m)
    (hd : d < m) :
    ((t - 1).descFactorial d : ℝ) / ((m - 1).descFactorial d : ℝ) ≤
      ((t : ℝ) / (m : ℝ)) ^ d := by
  have hmNat : 0 < m := by omega
  have hm : (0 : ℝ) < m := Nat.cast_pos.mpr hmNat
  have hdenNat : 0 < (m - 1).descFactorial d := by
    apply Nat.pos_of_ne_zero
    intro hz
    have hlt := Nat.descFactorial_eq_zero_iff_lt.mp hz
    omega
  have hden : (0 : ℝ) < ((m - 1).descFactorial d : ℝ) := Nat.cast_pos.mpr hdenNat
  rw [div_pow]
  apply (div_le_div_iff₀ hden (pow_pos hm d)).mpr
  have h := descFactorial_mul_pow_le ht htm d
  rw [mul_comm ((t : ℝ) ^ d)]
  exact_mod_cast h

end Kahn
