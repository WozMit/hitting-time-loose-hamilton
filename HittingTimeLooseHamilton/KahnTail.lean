module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.GCongr
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Push

public section

open Finset

namespace KahnEntropy

/-- An elementary lower bound on the logarithm of a factorial. -/
theorem log_factorial_lower (n : ℕ) :
    (n : ℝ) * Real.log n - n ≤ ∑ i ∈ range n, Real.log ((i : ℝ) + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ]
    by_cases hn : n = 0
    · subst n
      norm_num
    have hnpos : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
    have hratio : 0 < ((n : ℝ) + 1) / n := div_pos (by positivity) hnpos
    have hlog := Real.log_le_sub_one_of_pos hratio
    rw [Real.log_div (by positivity) hnpos.ne'] at hlog
    have hmul := mul_le_mul_of_nonneg_left hlog hnpos.le
    have heq : (n : ℝ) * (((n : ℝ) + 1) / n - 1) = 1 := by
      field_simp [hnpos.ne'] <;> ring
    rw [heq] at hmul
    push_cast
    nlinarith

/-- The logarithmic contribution of the first block is bounded linearly. -/
theorem sum_log_ratio_le (n : ℕ) :
    (∑ i ∈ range n, Real.log ((n : ℝ) / ((i : ℝ) + 1))) ≤ n := by
  have h := log_factorial_lower n
  by_cases hn : n = 0
  · subst n
    simp
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have heq : (∑ i ∈ range n, Real.log ((n : ℝ) / ((i : ℝ) + 1))) =
      n * Real.log n - ∑ i ∈ range n, Real.log ((i : ℝ) + 1) := by
    calc
      _ = ∑ i ∈ range n, (Real.log (n : ℝ) - Real.log ((i : ℝ) + 1)) := by
        apply sum_congr rfl
        intro i hi
        exact Real.log_div hn0 (by positivity)
      _ = _ := by rw [sum_sub_distrib]; simp
  rw [heq]
  linarith

/-- A reciprocal square is bounded by a telescoping difference. -/
theorem inv_sq_le_difference {x : ℝ} (hx : 1 < x) :
    1 / x ^ 2 ≤ 1 / (x - 1) - 1 / x := by
  have hxp : 0 < x := by linarith
  have hxm : 0 < x - 1 := by linarith
  calc
    1 / x ^ 2 ≤ 1 / ((x - 1) * x) :=
      one_div_le_one_div_of_le (mul_pos hxm hxp) (by nlinarith)
    _ = 1 / (x - 1) - 1 / x := by
      field_simp [hxm.ne', hxp.ne'] <;> ring

/-- Below the cutoff the logarithm is dominated by a constant plus a logarithmic ratio. -/
theorem log_one_add_pow_le_of_one_le {x : ℝ} (hx : 1 ≤ x) (d : ℕ) :
    Real.log (1 + x ^ d) ≤ Real.log 2 + d * Real.log x := by
  have hxpos : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hp : 1 ≤ x ^ d := one_le_pow₀ hx
  calc
    Real.log (1 + x ^ d) ≤ Real.log (2 * x ^ d) :=
      Real.log_le_log (by positivity) (by linarith)
    _ = Real.log 2 + d * Real.log x := by
      rw [Real.log_mul (by norm_num) (pow_ne_zero _ hxpos.ne'), Real.log_pow]

/-- Beyond the cutoff, every power at least two has a square majorant. -/
theorem log_one_add_pow_le_square {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    {d : ℕ} (hd : 2 ≤ d) : Real.log (1 + x ^ d) ≤ x ^ 2 := by
  calc
    Real.log (1 + x ^ d) ≤ (1 + x ^ d) - 1 :=
      Real.log_le_sub_one_of_pos (by positivity)
    _ = x ^ d := by ring
    _ ≤ x ^ 2 := pow_le_pow_of_le_one hx0 hx1 hd

/-- Uniform estimate for a shifted reciprocal-square tail. -/
theorem sum_inv_sq_le {k : ℕ} (hk : 0 < k) (m : ℕ) :
    (∑ i ∈ range m, 1 / (((k + i : ℕ) : ℝ) + 1) ^ 2) ≤
      1 / (k : ℝ) - 1 / ((k + m : ℕ) : ℝ) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [sum_range_succ]
    have hkm : (0 : ℝ) < ((k + m : ℕ) : ℝ) := by exact_mod_cast Nat.add_pos_left hk m
    have h := inv_sq_le_difference (x := ((k + m : ℕ) : ℝ) + 1) (by linarith)
    simp only [add_sub_cancel_right] at h
    push_cast at *
    simp only [add_assoc] at *
    linarith

/-- The first block in the entropy error sum. -/
theorem head_sum_le {a : ℝ} (ha : 0 ≤ a) {k : ℕ} (hak : a ≤ k) (d : ℕ) :
    (∑ i ∈ range k, Real.log (1 + (a / ((i : ℝ) + 1)) ^ d)) ≤
      (k : ℝ) * (Real.log 2 + d) := by
  have hpoint : ∀ i ∈ range k,
      Real.log (1 + (a / ((i : ℝ) + 1)) ^ d) ≤
        Real.log 2 + (d : ℝ) * Real.log ((k : ℝ) / ((i : ℝ) + 1)) := by
    intro i hi
    have hi' : (i : ℝ) + 1 ≤ k := by exact_mod_cast Nat.succ_le_of_lt (mem_range.mp hi)
    have hden : (0 : ℝ) < (i : ℝ) + 1 := by positivity
    have hratio : (1 : ℝ) ≤ k / ((i : ℝ) + 1) := (le_div_iff₀ hden).mpr (by simpa using hi')
    apply le_trans _ (log_one_add_pow_le_of_one_le hratio d)
    apply Real.log_le_log (by positivity)
    apply add_le_add_right
    exact pow_le_pow_left₀ (div_nonneg ha hden.le) (div_le_div_of_nonneg_right hak hden.le) d
  calc
    _ ≤ ∑ i ∈ range k, (Real.log 2 + (d : ℝ) * Real.log ((k : ℝ) / ((i : ℝ) + 1))) :=
      sum_le_sum hpoint
    _ = (k : ℝ) * Real.log 2 + d * ∑ i ∈ range k, Real.log ((k : ℝ) / ((i : ℝ) + 1)) := by
      rw [sum_add_distrib, ← mul_sum]
      simp
    _ ≤ (k : ℝ) * Real.log 2 + d * k := by
      gcongr
      exact sum_log_ratio_le k
    _ = _ := by ring

/-- The remaining block in the entropy error sum. -/
theorem tail_sum_le {a : ℝ} (ha : 0 ≤ a) {k : ℕ} (hk : 0 < k) (hak : a ≤ k)
    {d : ℕ} (hd : 2 ≤ d) (m : ℕ) :
    (∑ i ∈ range m, Real.log (1 + (a / (((k + i : ℕ) : ℝ) + 1)) ^ d)) ≤ k := by
  have hpoint : ∀ i ∈ range m,
      Real.log (1 + (a / (((k + i : ℕ) : ℝ) + 1)) ^ d) ≤
        (k : ℝ) ^ 2 * (1 / (((k + i : ℕ) : ℝ) + 1) ^ 2) := by
    intro i hi
    have hden : (0 : ℝ) < ((k + i : ℕ) : ℝ) + 1 := by positivity
    have hak' : a ≤ ((k + i : ℕ) : ℝ) + 1 := by
      push_cast
      linarith [Nat.cast_nonneg (α := ℝ) i]
    have hratio : a / (((k + i : ℕ) : ℝ) + 1) ≤ 1 := (div_le_one hden).mpr hak'
    calc
      _ ≤ (a / (((k + i : ℕ) : ℝ) + 1)) ^ 2 :=
        log_one_add_pow_le_square (div_nonneg ha hden.le) hratio hd
      _ ≤ ((k : ℝ) / (((k + i : ℕ) : ℝ) + 1)) ^ 2 :=
        pow_le_pow_left₀ (div_nonneg ha hden.le) (div_le_div_of_nonneg_right hak hden.le) 2
      _ = _ := by rw [div_pow]; ring
  have hkpos : (0 : ℝ) < k := Nat.cast_pos.mpr hk
  calc
    _ ≤ ∑ i ∈ range m, (k : ℝ) ^ 2 * (1 / (((k + i : ℕ) : ℝ) + 1) ^ 2) :=
      sum_le_sum hpoint
    _ = (k : ℝ) ^ 2 * ∑ i ∈ range m, 1 / (((k + i : ℕ) : ℝ) + 1) ^ 2 := by rw [mul_sum]
    _ ≤ (k : ℝ) ^ 2 * (1 / k - 1 / ((k + m : ℕ) : ℝ)) :=
      mul_le_mul_of_nonneg_left (sum_inv_sq_le hk m) (sq_nonneg _)
    _ ≤ (k : ℝ) ^ 2 * (1 / k) := by
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
      exact sub_le_self _ (by positivity)
    _ = k := by field_simp [hkpos.ne'] <;> ring

/-- A finite entropy-error sum, with an arbitrary integral cutoff. -/
theorem entropy_error_sum_le_cutoff {a : ℝ} (ha : 0 ≤ a) {k : ℕ} (hk : 0 < k)
    (hak : a ≤ k) {d : ℕ} (hd : 2 ≤ d) (m : ℕ) :
    (∑ i ∈ range m, Real.log (1 + (a / ((i : ℝ) + 1)) ^ d)) ≤
      ((d : ℝ) + 2) * k := by
  have hmono : (∑ i ∈ range m, Real.log (1 + (a / ((i : ℝ) + 1)) ^ d)) ≤
      ∑ i ∈ range (k + m), Real.log (1 + (a / ((i : ℝ) + 1)) ^ d) := by
    apply sum_le_sum_of_subset_of_nonneg (range_mono (Nat.le_add_left m k))
    intro i hi him
    apply Real.log_nonneg
    have : 0 ≤ (a / ((i : ℝ) + 1)) ^ d := by positivity
    linarith
  have hhead := head_sum_le ha hak d
  have htail := tail_sum_le ha hk hak hd m
  have hlog2 : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have hlog2k := mul_le_mul_of_nonneg_left hlog2 (Nat.cast_nonneg (α := ℝ) k)
  rw [sum_range_add] at hmono
  push_cast at htail hmono
  nlinarith [Nat.cast_nonneg (α := ℝ) k]

/-- A uniform estimate of the required order, with an explicit constant. -/
theorem entropy_error_sum_le {a : ℝ} (ha : 0 ≤ a) {d : ℕ} (hd : 2 ≤ d) (m : ℕ) :
    (∑ i ∈ range m, Real.log (1 + (a / ((i : ℝ) + 1)) ^ d)) ≤
      (2 * ((d : ℝ) + 2)) * (a + 1) := by
  have hak : a ≤ ((⌈a⌉₊ + 1 : ℕ) : ℝ) := by
    have h := Nat.le_ceil a
    push_cast
    linarith
  have h := entropy_error_sum_le_cutoff ha (Nat.succ_pos ⌈a⌉₊) hak hd m
  have hceil := Nat.ceil_lt_add_one ha
  have hcutoff : (⌈a⌉₊ : ℝ) + 1 ≤ 2 * (a + 1) := by linarith
  have hmul := mul_le_mul_of_nonneg_left hcutoff (show (0 : ℝ) ≤ (d : ℝ) + 2 by positivity)
  push_cast at h
  nlinarith

/-- The analytic error estimate in the parameters used by the entropy argument. -/
theorem entropy_error_sum_scaled {γ : ℝ} (hγ : 0 ≤ γ) {d : ℕ} (hd : 2 ≤ d) (m : ℕ) :
    (∑ i ∈ range m, Real.log (1 + γ * ((m : ℝ) / ((i : ℝ) + 1)) ^ d)) ≤
      (2 * ((d : ℝ) + 2)) * ((m : ℝ) * γ ^ ((d : ℝ)⁻¹) + 1) := by
  have hd0 : d ≠ 0 := by omega
  have hpow : (γ ^ ((d : ℝ)⁻¹)) ^ d = γ := Real.rpow_inv_natCast_pow hγ hd0
  have h := entropy_error_sum_le (a := (m : ℝ) * γ ^ ((d : ℝ)⁻¹)) (by positivity) hd m
  convert h using 1
  apply sum_congr rfl
  intro i hi
  congr 2
  simp only [div_pow, mul_pow, hpow]
  ring

/-- A matching elementary upper bound, sufficient for the factorial baseline. -/
theorem log_factorial_upper (n : ℕ) :
    (∑ i ∈ range n, Real.log ((i : ℝ) + 1)) ≤
      ((n : ℝ) + 1) * Real.log n - n + 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ]
    by_cases hn : n = 0
    · subst n
      norm_num
    have hnpos : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
    have hratio : 0 < (n : ℝ) / ((n : ℝ) + 1) := div_pos hnpos (by positivity)
    have hlog := Real.log_le_sub_one_of_pos hratio
    rw [Real.log_div hnpos.ne' (by positivity)] at hlog
    have hmul := mul_le_mul_of_nonneg_left hlog (by positivity : (0 : ℝ) ≤ (n : ℝ) + 1)
    have heq : ((n : ℝ) + 1) * ((n : ℝ) / ((n : ℝ) + 1) - 1) = -1 := by
      field_simp <;> ring
    rw [heq] at hmul
    push_cast
    nlinarith

/-- The factorial baseline in the entropy calculation. -/
theorem sum_log_normalized_le {n : ℕ} (hn : 0 < n) :
    (∑ i ∈ range n, Real.log (((i : ℝ) + 1) / n)) ≤ -n + 1 + Real.log n := by
  have h := log_factorial_upper n
  have hn0 : (n : ℝ) ≠ 0 := (Nat.cast_pos.mpr hn).ne'
  have heq : (∑ i ∈ range n, Real.log (((i : ℝ) + 1) / n)) =
      (∑ i ∈ range n, Real.log ((i : ℝ) + 1)) - n * Real.log n := by
    calc
      _ = ∑ i ∈ range n, (Real.log ((i : ℝ) + 1) - Real.log (n : ℝ)) := by
        apply sum_congr rfl
        intro i hi
        exact Real.log_div (by positivity) hn0
      _ = _ := by rw [sum_sub_distrib]; simp
  rw [heq]
  nlinarith

/-- Splitting the logarithm into the factorial baseline and its perturbation. -/
theorem log_pow_add_split {t m γ : ℝ} (ht : 0 < t) (hm : 0 < m)
    (hγ : 0 ≤ γ) (d : ℕ) :
    Real.log ((t / m) ^ d + γ) =
      (d : ℝ) * Real.log (t / m) + Real.log (1 + γ * (m / t) ^ d) := by
  have hid : (t / m) ^ d + γ = (t / m) ^ d * (1 + γ * (m / t) ^ d) := by
    rw [div_pow, div_pow]
    field_simp [ht.ne', hm.ne'] <;> ring
  rw [hid, Real.log_mul (by positivity) (by positivity), Real.log_pow]

/-- The entire analytic penalty estimate in the finite entropy argument. -/
theorem local_penalty_le {m d : ℕ} (hm : 0 < m) (hd : 2 ≤ d)
    {γ : ℝ} (hγ : 0 ≤ γ) :
    (∑ i ∈ range m, Real.log ((((i : ℝ) + 1) / m) ^ d + γ)) ≤
      -(d : ℝ) * m + d * (1 + Real.log m) +
        (2 * ((d : ℝ) + 2)) * ((m : ℝ) * γ ^ ((d : ℝ)⁻¹) + 1) := by
  have hsplit :
      (∑ i ∈ range m, Real.log ((((i : ℝ) + 1) / m) ^ d + γ)) =
        (d : ℝ) * (∑ i ∈ range m, Real.log (((i : ℝ) + 1) / m)) +
          ∑ i ∈ range m, Real.log (1 + γ * ((m : ℝ) / ((i : ℝ) + 1)) ^ d) := by
    calc
      _ = ∑ i ∈ range m, ((d : ℝ) * Real.log (((i : ℝ) + 1) / m) +
          Real.log (1 + γ * ((m : ℝ) / ((i : ℝ) + 1)) ^ d)) := by
        apply sum_congr rfl
        intro i hi
        exact log_pow_add_split (by positivity) (Nat.cast_pos.mpr hm) hγ d
      _ = _ := by rw [sum_add_distrib, mul_sum]
  rw [hsplit]
  have hbase := mul_le_mul_of_nonneg_left (sum_log_normalized_le hm) (Nat.cast_nonneg (α := ℝ) d)
  have herr := entropy_error_sum_scaled hγ hd m
  nlinarith

end KahnEntropy
