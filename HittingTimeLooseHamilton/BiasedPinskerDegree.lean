module

public import HittingTimeLooseHamilton.BiasedPinsker

public section

noncomputable section
open scoped BigOperators
namespace FiniteEntropy

/-- A reverse relative-entropy estimate for positive numbers of mean one.
No upper bound on the individual numbers is needed. -/
theorem mean_one_l1_sq_le_log_deficit {I : Type*} [Fintype I]
    (x : I → ℝ) (hx : ∀ i, 0 < x i)
    (hmean : ∑ i, x i = (Fintype.card I : ℝ)) :
    (∑ i, |x i - 1|)^2 ≤
      4 * (Fintype.card I : ℝ) * (-∑ i, Real.log (x i)) := by
  have hh : (∑ i, (1 - Real.sqrt (x i))^2) ≤ -∑ i, Real.log (x i) := by
    have h := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset I)) =>
      sqrt_sub_sq_le_log 1 (x i) (by norm_num) (hx i))
    simpa only [Real.sqrt_one, Real.log_one, mul_zero, zero_sub, one_mul,
      Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_neg_distrib,
      Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, hmean,
      sub_add_cancel] using h
  have hfactor (i : I) : |x i - 1| =
      |1 - Real.sqrt (x i)| * (1 + Real.sqrt (x i)) := by
    rw [← abs_of_nonneg (show 0 ≤ 1 + Real.sqrt (x i) by positivity), ← abs_mul]
    have heq : (1 - Real.sqrt (x i)) * (1 + Real.sqrt (x i)) = -(x i - 1) := by
      nlinarith [Real.sq_sqrt (hx i).le]
    rw [heq, abs_neg]
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset I)
    (fun i => |1 - Real.sqrt (x i)|) (fun i => 1 + Real.sqrt (x i))
  simp only [sq_abs, ← hfactor] at hcs
  have hupper : (∑ i, (1 + Real.sqrt (x i))^2) ≤ 4 * (Fintype.card I : ℝ) := by
    calc
      _ ≤ ∑ i, (2 + 2 * x i) := by
        apply Finset.sum_le_sum
        intro i _
        nlinarith [Real.sq_sqrt (hx i).le, sq_nonneg (1 - Real.sqrt (x i))]
      _ = _ := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, hmean]
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        ring
  have hnonneg : 0 ≤ ∑ i, (1 - Real.sqrt (x i))^2 :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hcard : 0 ≤ (Fintype.card I : ℝ) := Nat.cast_nonneg _
  calc
    _ ≤ (∑ i, (1 - Real.sqrt (x i))^2) * (∑ i, (1 + Real.sqrt (x i))^2) := hcs
    _ ≤ (∑ i, (1 - Real.sqrt (x i))^2) * (4 * (Fintype.card I : ℝ)) :=
      mul_le_mul_of_nonneg_left hupper hnonneg
    _ ≤ (-∑ i, Real.log (x i)) * (4 * (Fintype.card I : ℝ)) :=
      mul_le_mul_of_nonneg_right hh (by positivity)
    _ = _ := by ring

/-- Degree irregularity is controlled by the logarithmic degree deficit. -/
theorem degree_l1_sq_le_log_deficit {I : Type*} [Fintype I]
    (d : I → ℝ) (lam : ℝ) (hlam : 0 < lam) (hd : ∀ i, 0 < d i)
    (hmean : ∑ i, d i = (Fintype.card I : ℝ) * lam) :
    (∑ i, |d i / lam - 1|)^2 ≤
      4 * (Fintype.card I : ℝ) *
        ((Fintype.card I : ℝ) * Real.log lam - ∑ i, Real.log (d i)) := by
  have hnormalized : (∑ i, d i / lam) = (Fintype.card I : ℝ) := by
    rw [← Finset.sum_div, hmean, mul_div_cancel_right₀ _ hlam.ne']
  have h := mean_one_l1_sq_le_log_deficit (fun i => d i / lam)
    (fun i => div_pos (hd i) hlam) hnormalized
  simp_rw [Real.log_div (hd _).ne' hlam.ne'] at h
  simpa only [Finset.sum_sub_distrib, neg_sub, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul] using h

/-- Square-root version of the logarithmic degree-deficit estimate. -/
theorem degree_l1_le_two_sqrt_log_deficit {I : Type*} [Fintype I]
    (d : I → ℝ) (lam : ℝ) (hlam : 0 < lam) (hd : ∀ i, 0 < d i)
    (hmean : ∑ i, d i = (Fintype.card I : ℝ) * lam) :
    (∑ i, |d i / lam - 1|) ≤
      2 * Real.sqrt ((Fintype.card I : ℝ) *
        ((Fintype.card I : ℝ) * Real.log lam - ∑ i, Real.log (d i))) := by
  have h := degree_l1_sq_le_log_deficit d lam hlam hd hmean
  have hn : 0 ≤ (Fintype.card I : ℝ) *
      ((Fintype.card I : ℝ) * Real.log lam - ∑ i, Real.log (d i)) := by
    nlinarith [sq_nonneg (∑ i, |d i / lam - 1|)]
  nlinarith [Real.sq_sqrt hn, Real.sqrt_nonneg ((Fintype.card I : ℝ) *
    ((Fintype.card I : ℝ) * Real.log lam - ∑ i, Real.log (d i)))]

end FiniteEntropy
