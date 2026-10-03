module

public import Mathlib

public section

/-! Quantitative normalized falling-factorial estimates. -/
noncomputable section
namespace LooseHamilton

@[expose] def normalizedFalling (k n d : ℕ) : ℝ := (k.descFactorial d:ℝ)/(n:ℝ)^d

lemma normalizedFalling_zero (k n : ℕ) : normalizedFalling k n 0=1 := by simp [normalizedFalling]
lemma normalizedFalling_succ (k n d : ℕ) :
    normalizedFalling k n (d+1)=((k-d:ℕ):ℝ)/n*normalizedFalling k n d := by
  simp only [normalizedFalling,Nat.descFactorial_succ,Nat.cast_mul,pow_succ]
  ring

lemma normalizedFalling_mem {k n : ℕ} (hkn : k≤n) (d : ℕ) :
    0≤normalizedFalling k n d ∧ normalizedFalling k n d≤1 := by
  induction d with
  | zero => simp [normalizedFalling_zero]
  | succ d ih =>
    rw [normalizedFalling_succ]
    have hfrac : ((k-d:ℕ):ℝ)/(n:ℝ)≤1 := by
      by_cases hn : n=0
      · simp [hn]
      apply (div_le_one (by exact_mod_cast (show 0<n by omega))).mpr
      exact_mod_cast (show k-d≤n by omega)
    constructor
    · exact mul_nonneg (by positivity) ih.1
    · exact (mul_le_mul_of_nonneg_right hfrac ih.1).trans (by simpa using ih.2)

lemma normalized_nat_sub_error {k n d : ℕ} {a : ℝ} (hn : 0<n) :
    |((k-d:ℕ):ℝ)/(n:ℝ)-a|≤|(k:ℝ)/(n:ℝ)-a|+(d:ℝ)/n := by
  have hn0 : (0:ℝ)<n := by exact_mod_cast hn
  have hd : |((k-d:ℕ):ℝ)-(k:ℝ)|≤d := by
    by_cases hk : d≤k
    · rw [Nat.cast_sub hk]
      have : (0:ℝ)≤d := Nat.cast_nonneg _
      rw [show (k:ℝ)-(d:ℝ)-k= -(d:ℝ) by ring,abs_neg,abs_of_nonneg this]
    · rw [Nat.sub_eq_zero_of_le (by omega)]
      simp only [Nat.cast_zero,zero_sub,abs_neg,abs_of_nonneg (Nat.cast_nonneg k : (0:ℝ)≤k)]
      exact_mod_cast (show k≤d by omega)
  calc
    _ = |((k-d:ℕ):ℝ)/(n:ℝ)-(k:ℝ)/(n:ℝ)+((k:ℝ)/(n:ℝ)-a)| := by congr 1; ring
    _ ≤ |((k-d:ℕ):ℝ)/(n:ℝ)-(k:ℝ)/(n:ℝ)|+|(k:ℝ)/(n:ℝ)-a| := abs_add_le _ _
    _ ≤ (d:ℝ)/n+|(k:ℝ)/(n:ℝ)-a| := by
      apply add_le_add_left
      rw [←sub_div,abs_div,abs_of_pos hn0]
      exact div_le_div_of_nonneg_right hd hn0.le
    _ = _ := by ring

lemma normalizedFalling_error {k n : ℕ} {a : ℝ} (hn : 0<n) (hkn : k≤n)
    (ha0 : 0≤a) (ha1 : a≤1) (d : ℕ) :
    |normalizedFalling k n d-a^d|≤(d:ℝ)*(|(k:ℝ)/(n:ℝ)-a|+(d:ℝ)/n) := by
  induction d with
  | zero => simp [normalizedFalling_zero]
  | succ d ih =>
    have hf := normalizedFalling_mem hkn d
    have hn0 : (0:ℝ)<n := by exact_mod_cast hn
    have hu := normalized_nat_sub_error (k:=k) (n:=n) (d:=d) (a:=a) hn
    have he := abs_nonneg ((k:ℝ)/(n:ℝ)-a)
    rw [normalizedFalling_succ,pow_succ]
    calc
      _ = |(((k-d:ℕ):ℝ)/(n:ℝ)-a)*normalizedFalling k n d+
          a*(normalizedFalling k n d-a^d)| := by congr 1; ring
      _ ≤ |(((k-d:ℕ):ℝ)/(n:ℝ)-a)*normalizedFalling k n d|+
          |a*(normalizedFalling k n d-a^d)| := abs_add_le _ _
      _ ≤ |((k-d:ℕ):ℝ)/(n:ℝ)-a|+|normalizedFalling k n d-a^d| := by
        rw [abs_mul,abs_of_nonneg hf.1,abs_mul,abs_of_nonneg ha0]
        exact add_le_add (by nlinarith [abs_nonneg (((k-d:ℕ):ℝ)/(n:ℝ)-a)])
          (by nlinarith [abs_nonneg (normalizedFalling k n d-a^d)])
      _ ≤ (d+1:ℕ)*(|(k:ℝ)/(n:ℝ)-a|+((d+1:ℕ):ℝ)/n) := by
        push_cast
        have hd : (0:ℝ)≤d := Nat.cast_nonneg _
        have hinv : (0:ℝ)≤1/n := by positivity
        rw [add_div] 
        nlinarith
end LooseHamilton
