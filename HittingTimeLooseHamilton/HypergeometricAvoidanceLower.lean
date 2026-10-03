module

public import HittingTimeLooseHamilton.HypergeometricAlgebra
public import Mathlib.Data.Nat.Factorial.BigOperators
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

public section

/-! A lower bound for avoidance, needed by the isolated-vertex second moment. -/
noncomputable section
namespace LooseHamilton.Hypergeometric
open Finset
open scoped BigOperators

lemma choose_ratio_eq_prod {a N t : ℕ} :
    (a.choose t : ℝ) / (N.choose t : ℝ) =
      ∏ i ∈ range t, ((a-i : ℕ) : ℝ) / ((N-i : ℕ) : ℝ) := by
  have hf : (t.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  calc
    (a.choose t : ℝ) / (N.choose t : ℝ) =
        (a.descFactorial t : ℝ) / (N.descFactorial t : ℝ) := by
      rw [Nat.descFactorial_eq_factorial_mul_choose,
        Nat.descFactorial_eq_factorial_mul_choose, Nat.cast_mul, Nat.cast_mul]
      exact (mul_div_mul_left _ _ hf).symm
    _ = _ := by simp only [Nat.descFactorial_eq_prod_range, Nat.cast_prod, prod_div_distrib]

/-- Lower comparison retaining the correction from sampling without replacement. -/
lemma avoidance_ratio_ge_pow {N m t : ℕ} (h : m + t < N) :
    (1 - (m : ℝ) / (N-t : ℕ))^t ≤
      ((N-t).choose m : ℝ) / (N.choose m : ℝ) := by
  have hm : m ≤ N := by omega
  have ht : t ≤ N-m := by omega
  rw [avoidance_ratio_dual hm ht, choose_ratio_eq_prod]
  have hd : (0 : ℝ) < (N-t : ℕ) := Nat.cast_pos.mpr (by omega)
  have hbase : 0 ≤ 1 - (m : ℝ) / (N-t : ℕ) := by
    apply sub_nonneg.mpr
    apply (div_le_one hd).mpr
    exact_mod_cast (show m ≤ N-t by omega)
  calc
    (1 - (m : ℝ) / (N-t : ℕ))^t =
        ∏ _i ∈ range t, (1 - (m : ℝ) / (N-t : ℕ)) := by simp
    _ ≤ _ := by
      apply prod_le_prod₀ (fun _ _ => hbase)
      intro i hi
      have hi' : i < t := mem_range.mp hi
      have hdi : (0 : ℝ) < (N-i : ℕ) := Nat.cast_pos.mpr (by omega)
      rw [le_div_iff₀ hdi]
      have hcast : ((N-m-i : ℕ) : ℝ) = (N-i : ℕ) - (m : ℝ) := by
        rw [show N-m-i = N-i-m by omega, Nat.cast_sub (by omega : m ≤ N-i)]
      rw [hcast]
      have hle : ((N-t : ℕ) : ℝ) ≤ (N-i : ℕ) := by exact_mod_cast (show N-t ≤ N-i by omega)
      have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg _
      have he : (m : ℝ) / (N-t : ℕ) * (N-t : ℕ) = m := div_mul_cancel₀ _ (ne_of_gt hd)
      have hmul := mul_le_mul_of_nonneg_left hle (div_nonneg hm0 hd.le)
      nlinarith

/-- Exponential lower bound for the probability that a fixed support is avoided. -/
lemma avoidance_ratio_ge_exp {N m t : ℕ} (h : m + t < N) :
    Real.exp (-((t : ℝ) * m / (N-m-t : ℕ))) ≤
      ((N-t).choose m : ℝ) / (N.choose m : ℝ) := by
  have hd : (0 : ℝ) < (N-t : ℕ) := Nat.cast_pos.mpr (by omega)
  have he : (0 : ℝ) < (N-m-t : ℕ) := Nat.cast_pos.mpr (by omega)
  have hc : ((N-t : ℕ) : ℝ) = (N-m-t : ℕ) + (m : ℝ) := by
    exact_mod_cast (show N-t = (N-m-t)+m by omega)
  have hy : 0 < 1 - (m : ℝ)/(N-t : ℕ) := by
    apply sub_pos.mpr
    apply (div_lt_one hd).mpr
    linarith
  have hlog := Real.one_sub_inv_le_log_of_pos hy
  have hidentity : 1 - (1 - (m : ℝ)/(N-t : ℕ))⁻¹ = -(m : ℝ)/(N-m-t : ℕ) := by
    rw [hc]
    field_simp [ne_of_gt he]
    <;> ring
  rw [hidentity] at hlog
  have hmul := mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg t : (0 : ℝ) ≤ t)
  calc
    Real.exp (-((t : ℝ)*m/(N-m-t : ℕ))) ≤
        Real.exp ((t : ℝ)*Real.log (1-(m : ℝ)/(N-t : ℕ))) := by
      apply Real.exp_le_exp.mpr
      convert hmul using 1 <;> ring
    _ = (1-(m : ℝ)/(N-t : ℕ))^t := by
      rw [Real.exp_nat_mul, Real.exp_log hy]
    _ ≤ _ := avoidance_ratio_ge_pow h
/-- Exponential upper comparison for joint avoidance. -/
lemma avoidance_ratio_le_exp {N m t : ℕ} (hm : m ≤ N) (hN : 0 < N) (ht : t ≤ N) :
    ((N-t).choose m : ℝ) / (N.choose m : ℝ) ≤
      Real.exp (-((t : ℝ)*m/N)) := by
  have hbase : 0 ≤ 1 - (m : ℝ)/N := by
    apply sub_nonneg.mpr
    apply (div_le_one (Nat.cast_pos.mpr hN)).mpr
    exact_mod_cast hm
  have hle : 1 - (m : ℝ)/N ≤ Real.exp (-(m : ℝ)/N) := by
    have := Real.add_one_le_exp (-(m : ℝ)/N)
    simpa only [neg_div, sub_eq_add_neg, add_comm] using this
  calc
    _ ≤ (1-(m : ℝ)/N)^t := avoidance_ratio_le hm hN ht
    _ ≤ (Real.exp (-(m : ℝ)/N))^t := pow_le_pow_left₀ hbase hle _
    _ = _ := by rw [← Real.exp_nat_mul]; congr 1; ring
end LooseHamilton.Hypergeometric
