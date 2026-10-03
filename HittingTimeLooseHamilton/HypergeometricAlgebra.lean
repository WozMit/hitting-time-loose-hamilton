module

public import Mathlib.Data.Nat.Choose.Cast
public import Mathlib.Data.Real.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Positivity

public section

noncomputable section
namespace LooseHamilton.Hypergeometric

/-- Sampling without replacement makes joint avoidance no more likely than
independent avoidance with the same one-element marginal. -/
lemma descFactorial_mul_pow_le {a N : ℕ} (ha : a ≤ N) (t : ℕ) :
    a.descFactorial t * N ^ t ≤ N.descFactorial t * a ^ t := by
  induction t with
  | zero => simp
  | succ t ih =>
    by_cases hsmall : a ≤ t
    · rw [Nat.descFactorial_eq_zero_iff_lt.mpr (by omega : a < t + 1), zero_mul]
      exact Nat.zero_le _
    · have h1 : a - t + t = a := by omega
      have h2 : N - t + t = N := by omega
      have h3 : t * a ≤ t * N := Nat.mul_le_mul_left _ ha
      have hf : (a - t) * N ≤ (N - t) * a := by nlinarith
      calc
        a.descFactorial (t + 1) * N ^ (t + 1) =
          (a.descFactorial t * N ^ t) * ((a - t) * N) := by
            rw [Nat.descFactorial_succ, pow_succ]; ring
        _ ≤ (N.descFactorial t * a ^ t) * ((N - t) * a) := Nat.mul_le_mul ih hf
        _ = N.descFactorial (t + 1) * a ^ (t + 1) := by
          rw [Nat.descFactorial_succ, pow_succ]; ring

lemma choose_ratio_le_pow {a N t : ℕ} (ha : a ≤ N) (hN : 0 < N) (ht : t ≤ N) :
    (a.choose t : ℝ) / (N.choose t : ℝ) ≤ ((a : ℝ) / N) ^ t := by
  have hc : (0 : ℝ) < N.choose t := Nat.cast_pos.mpr (Nat.choose_pos ht)
  have hn : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hf : (0 : ℝ) < t.factorial := Nat.cast_pos.mpr (Nat.factorial_pos _)
  have h := descFactorial_mul_pow_le ha t
  rw [Nat.descFactorial_eq_factorial_mul_choose, Nat.descFactorial_eq_factorial_mul_choose] at h
  have hr : (t.factorial : ℝ) * (a.choose t : ℝ) * (N : ℝ) ^ t ≤
      (t.factorial : ℝ) * (N.choose t : ℝ) * (a : ℝ) ^ t := by exact_mod_cast h
  rw [div_pow]
  apply (div_le_div_iff₀ hc (pow_pos hn _)).mpr
  nlinarith

/-- Exact avoidance ratio, expressed by sampling the forbidden elements instead. -/
lemma avoidance_ratio_dual {N m t : ℕ} (hm : m ≤ N) (ht : t ≤ N - m) :
    ((N - t).choose m : ℝ) / (N.choose m : ℝ) =
      ((N - m).choose t : ℝ) / (N.choose t : ℝ) := by
  have htm : m ≤ N - t := by omega
  have htN : t ≤ N := by omega
  rw [Nat.cast_choose ℝ htm, Nat.cast_choose ℝ hm, Nat.cast_choose ℝ ht, Nat.cast_choose ℝ htN]
  have hdiff : N - t - m = N - m - t := by omega
  rw [hdiff]
  field_simp <;> ring

/-- Hypergeometric avoidance bound in a universe of size N. -/
lemma avoidance_ratio_le {N m t : ℕ} (hm : m ≤ N) (hN : 0 < N) (ht : t ≤ N) :
    ((N - t).choose m : ℝ) / (N.choose m : ℝ) ≤
      (1 - (m : ℝ) / N) ^ t := by
  have hn : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have ha : 0 ≤ 1 - (m : ℝ) / N := by
    have hm' : (m : ℝ) ≤ N := by exact_mod_cast hm
    exact sub_nonneg.mpr ((div_le_one hn).mpr hm')
  by_cases htm : t ≤ N - m
  · rw [avoidance_ratio_dual hm htm]
    have h := choose_ratio_le_pow (Nat.sub_le N m) hN ht
    have heq : ((N - m : ℕ) : ℝ) / N = 1 - (m : ℝ) / N := by
      rw [Nat.cast_sub hm]
      field_simp
    rwa [heq] at h
  · rw [Nat.choose_eq_zero_of_lt (by omega : N - t < m), Nat.cast_zero, zero_div]
    exact pow_nonneg ha _

/-- Avoidance decreases with the number of sampled elements. -/
lemma avoidance_ratio_antitone {N d s t : ℕ} (hs : s ≤ N) (hd : d ≤ N) (ht : t ≤ s) :
    ((N - d).choose s : ℝ) / (N.choose s : ℝ) ≤
      ((N - d).choose t : ℝ) / (N.choose t : ℝ) := by
  by_cases hds : d ≤ N - s
  · rw [avoidance_ratio_dual hs hds, avoidance_ratio_dual (ht.trans hs) (by omega)]
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
    exact_mod_cast Nat.choose_le_choose d (Nat.sub_le_sub_left ht N)
  · rw [Nat.choose_eq_zero_of_lt (by omega : N - d < s), Nat.cast_zero, zero_div]
    positivity

end LooseHamilton.Hypergeometric
