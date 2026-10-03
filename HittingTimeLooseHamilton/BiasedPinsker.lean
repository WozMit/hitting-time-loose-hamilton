module

public import HittingTimeLooseHamilton.KahnEntropy
public import Mathlib.Data.Real.Sqrt

public section

noncomputable section
open scoped BigOperators
namespace FiniteEntropy

/-- Squared Hellinger distance is bounded by relative entropy, atom by atom. -/
lemma sqrt_sub_sq_le_log (x y : ℝ) (hx : 0 ≤ x) (hy : 0 < y) :
    (Real.sqrt x - Real.sqrt y)^2 ≤ x * Real.log x - x * Real.log y - x + y := by
  by_cases hz : x = 0
  · subst x
    simp [Real.sq_sqrt hy.le]
  have hx' : 0 < x := lt_of_le_of_ne hx (Ne.symm hz)
  have hsx := Real.sq_sqrt hx
  have hsy := Real.sq_sqrt hy.le
  have h := mul_log_ratio_le x (Real.sqrt x * Real.sqrt y) hx
    (mul_pos (Real.sqrt_pos.2 hx') (Real.sqrt_pos.2 hy))
  rw [Real.log_mul (Real.sqrt_pos.2 hx').ne' (Real.sqrt_pos.2 hy).ne',
    Real.log_sqrt hx, Real.log_sqrt hy.le] at h
  nlinarith

/-- Relative entropy controls the squared Hellinger distance of finite laws. -/
lemma hellinger_sq_le_relative_entropy {A : Type*} [Fintype A]
    (p q : Law A) (hq : ∀ a, 0 < q.mass a) :
    (∑ a, (Real.sqrt (p.mass a) - Real.sqrt (q.mass a))^2) ≤
      ∑ a, (p.mass a * Real.log (p.mass a) - p.mass a * Real.log (q.mass a)) := by
  have h := Finset.sum_le_sum (fun a (_ : a ∈ (Finset.univ : Finset A)) =>
    sqrt_sub_sq_le_log (p.mass a) (q.mass a) (p.nonneg a) (hq a))
  simpa only [Finset.sum_add_distrib, Finset.sum_sub_distrib, p.total, q.total,
    sub_add_cancel] using h

/-- A finite-law entropy-to-total-variation estimate; its absolute constant is
sufficient for asymptotic stability arguments. -/
theorem l1_sq_le_four_relative_entropy {A : Type*} [Fintype A]
    (p q : Law A) (hq : ∀ a, 0 < q.mass a) :
    (∑ a, |p.mass a - q.mass a|)^2 ≤
      4 * ∑ a, (p.mass a * Real.log (p.mass a) - p.mass a * Real.log (q.mass a)) := by
  have hfactor (a : A) : |p.mass a - q.mass a| =
      |Real.sqrt (p.mass a) - Real.sqrt (q.mass a)| *
        (Real.sqrt (p.mass a) + Real.sqrt (q.mass a)) := by
    rw [← abs_of_nonneg (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)), ← abs_mul]
    congr 1
    nlinarith [Real.sq_sqrt (p.nonneg a), Real.sq_sqrt (q.nonneg a)]
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset A)
    (fun a => |Real.sqrt (p.mass a) - Real.sqrt (q.mass a)|)
    (fun a => Real.sqrt (p.mass a) + Real.sqrt (q.mass a))
  simp only [sq_abs, ← hfactor] at hcs
  have hupper : (∑ a, (Real.sqrt (p.mass a) + Real.sqrt (q.mass a))^2) ≤ 4 := by
    calc
      _ ≤ ∑ a, (2 * p.mass a + 2 * q.mass a) := by
        apply Finset.sum_le_sum
        intro a _
        nlinarith [Real.sq_sqrt (p.nonneg a), Real.sq_sqrt (q.nonneg a),
          sq_nonneg (Real.sqrt (p.mass a) - Real.sqrt (q.mass a))]
      _ = 4 := by rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, p.total, q.total]; norm_num
  have hnonneg : 0 ≤ ∑ a, (Real.sqrt (p.mass a) - Real.sqrt (q.mass a))^2 :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hh := hellinger_sq_le_relative_entropy p q hq
  nlinarith [mul_le_mul_of_nonneg_left hupper hnonneg]

/-- Entropy deficit from the uniform law controls the L1 distance to uniform. -/
theorem l1_sq_le_four_entropy_deficit {A : Type*} [Fintype A] [Nonempty A]
    (p : Law A) :
    (∑ a, |p.mass a - (Fintype.card A : ℝ)⁻¹|)^2 ≤
      4 * (Real.log (Fintype.card A) - entropy p.mass) := by
  have h := l1_sq_le_four_relative_entropy p (uniform : Law A)
    (fun _ => inv_pos.mpr (Nat.cast_pos.mpr Fintype.card_pos))
  simpa only [uniform, Real.log_inv, mul_neg, sub_neg_eq_add, Finset.sum_add_distrib,
    ← Finset.sum_mul, p.total, one_mul, entropy, sub_neg_eq_add, add_comm] using h

/-- Square-root form of the finite-law stability estimate. -/
theorem l1_le_two_sqrt_entropy_deficit {A : Type*} [Fintype A] [Nonempty A]
    (p : Law A) :
    (∑ a, |p.mass a - (Fintype.card A : ℝ)⁻¹|) ≤
      2 * Real.sqrt (Real.log (Fintype.card A) - entropy p.mass) := by
  have h := l1_sq_le_four_entropy_deficit p
  have hd := sub_nonneg.mpr (entropy_le_log_card p)
  nlinarith [Real.sq_sqrt hd, Real.sqrt_nonneg (Real.log (Fintype.card A) - entropy p.mass)]

/-- Weighted Cauchy--Schwarz in the form used to aggregate marginal errors. -/
lemma weighted_sum_sq_le {I : Type*} [Fintype I] (w d : I → ℝ)
    (hw : ∀ i, 0 ≤ w i) :
    (∑ i, w i * d i)^2 ≤ (∑ i, w i) * (∑ i, w i * (d i)^2) := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset I)
    (fun i => Real.sqrt (w i)) (fun i => Real.sqrt (w i) * d i)
  have hmul (i : I) : Real.sqrt (w i) * (Real.sqrt (w i) * d i) = w i * d i := by
    rw [← mul_assoc, Real.mul_self_sqrt (hw i)]
  have hsq (i : I) : (Real.sqrt (w i) * d i)^2 = w i * (d i)^2 := by
    rw [mul_pow, Real.sq_sqrt (hw i)]
  simpa only [hmul, hsq, Real.sq_sqrt (hw _)] using h

/-- Averaging marginal entropy deficits costs a single square root. -/
lemma weighted_error_sq_le {I : Type*} [Fintype I] (w d D : I → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hbound : ∀ i, (d i)^2 ≤ 4 * D i) :
    (∑ i, w i * d i)^2 ≤ 4 * (∑ i, w i) * (∑ i, w i * D i) := by
  have hpoint : (∑ i, w i * (d i)^2) ≤ 4 * (∑ i, w i * D i) := by
    calc
      _ ≤ ∑ i, w i * (4 * D i) := Finset.sum_le_sum (fun i _ =>
        mul_le_mul_of_nonneg_left (hbound i) (hw i))
      _ = _ := by simp_rw [show ∀ i, w i * (4 * D i) = 4 * (w i * D i) by intro i; ring]; rw [Finset.mul_sum]
  have h := weighted_sum_sq_le w d hw
  have hmass := Finset.sum_nonneg (fun i (_ : i ∈ (Finset.univ : Finset I)) => hw i)
  nlinarith [mul_le_mul_of_nonneg_left hpoint hmass]

end FiniteEntropy
