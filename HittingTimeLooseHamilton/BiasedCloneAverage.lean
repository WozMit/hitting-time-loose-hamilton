module

public import HittingTimeLooseHamilton.BiasedCloneBalance

public section

noncomputable section
open scoped BigOperators
namespace FiniteEntropy

/-- Jensen's square-root inequality for a finite probability law, obtained from
weighted Cauchy--Schwarz. -/
lemma law_average_sqrt_le {R : Type*} [Fintype R] (q : Law R)
    (D : R → ℝ) (hD : ∀ a, 0 ≤ D a) :
    (∑ a, q.mass a * Real.sqrt (D a)) ≤ Real.sqrt (∑ a, q.mass a * D a) := by
  have h := weighted_sum_sq_le q.mass (fun a => Real.sqrt (D a)) q.nonneg
  simp only [q.total, one_mul, Real.sq_sqrt (hD _)] at h
  have hn : 0 ≤ ∑ a, q.mass a * D a :=
    Finset.sum_nonneg (fun a _ => mul_nonneg (q.nonneg a) (hD a))
  nlinarith [Real.sq_sqrt hn, Real.sqrt_nonneg (∑ a, q.mass a * D a)]

/-- Changing a reciprocal reference in an edge L1 sum. -/
lemma reciprocal_reference_l1 {E : Type*} [Fintype E]
    (p : E → ℝ) (lam lam₀ : ℝ) :
    (∑ e, |p e - 1 / lam₀|) ≤
      (∑ e, |p e - 1 / lam|) +
        (Fintype.card E : ℝ) * |1 / lam - 1 / lam₀| := by
  calc
    _ ≤ ∑ e, (|p e - 1 / lam| + |1 / lam - 1 / lam₀|) :=
      Finset.sum_le_sum (fun e _ => abs_sub_le _ _ _)
    _ = _ := by
      rw [Finset.sum_add_distrib]
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- The exact reference-change cost when the incidence count identifies the
number of edges with vertex count times average degree divided by uniformity. -/
lemma scaled_reciprocal_reference_l1 {E : Type*} [Fintype E]
    (p : E → ℝ) (r v lam lam₀ : ℝ) (hr : 0 ≤ r)
    (hlam : 0 < lam)
    (hcard : r * (Fintype.card E : ℝ) = v * lam) :
    r * (∑ e, |p e - 1 / lam₀|) ≤
      r * (∑ e, |p e - 1 / lam|) + v * |lam / lam₀ - 1| := by
  have hcost : r * ((Fintype.card E : ℝ) * |1 / lam - 1 / lam₀|) =
      v * |lam / lam₀ - 1| := by
    rw [← mul_assoc, hcard, mul_assoc]
    congr 1
    rw [show lam * |1 / lam - 1 / lam₀| = |lam * (1 / lam - 1 / lam₀)| by
      rw [abs_mul, abs_of_pos hlam]]
    have heq : lam * (1 / lam - 1 / lam₀) = -(lam / lam₀ - 1) := by
      rw [mul_sub, mul_one_div_cancel hlam.ne']
      ring
    rw [heq, abs_neg]
  have h := mul_le_mul_of_nonneg_left (reciprocal_reference_l1 p lam lam₀) hr
  simpa only [mul_add, hcost] using h

/-- Two nonnegative deficit contributions can share a single square root. -/
lemma sqrt_pair_le {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    Real.sqrt x + Real.sqrt y ≤ Real.sqrt (2 * (x + y)) := by
  have hn : 0 ≤ 2 * (x + y) := by positivity
  nlinarith [Real.sq_sqrt hx, Real.sq_sqrt hy, Real.sq_sqrt hn,
    Real.sqrt_nonneg (2 * (x + y)),
    sq_nonneg (Real.sqrt x - Real.sqrt y)]

/-- Average a family of clone-marginal estimates over a role law. This is purely
analytic: the caller proves the per-role estimate and supplies its actual local
entropy, degree, and reference-change deficits. -/
theorem average_clone_balance {R : Type*} [Fintype R]
    (q : Law R) (A D Q t : R → ℝ) (r v : ℝ) (hv : 0 ≤ v)
    (hD : ∀ a, 0 ≤ D a) (hQ : ∀ a, 0 ≤ Q a)
    (hlocal : ∀ a, r * A a ≤
      2 * Real.sqrt (v * D a) + 2 * Real.sqrt (v * Q a) + v * t a) :
    r * (∑ a, q.mass a * A a) ≤
      2 * Real.sqrt (2 * v * (∑ a, q.mass a * (D a + Q a))) +
        v * (∑ a, q.mass a * t a) := by
  have havg := Finset.sum_le_sum (fun a (_ : a ∈ (Finset.univ : Finset R)) =>
    mul_le_mul_of_nonneg_left (hlocal a) (q.nonneg a))
  have hDavg := law_average_sqrt_le q (fun a => v * D a)
    (fun a => mul_nonneg hv (hD a))
  have hQavg := law_average_sqrt_le q (fun a => v * Q a)
    (fun a => mul_nonneg hv (hQ a))
  have hDnonneg : 0 ≤ ∑ a, q.mass a * (v * D a) :=
    Finset.sum_nonneg (fun a _ => mul_nonneg (q.nonneg a) (mul_nonneg hv (hD a)))
  have hQnonneg : 0 ≤ ∑ a, q.mass a * (v * Q a) :=
    Finset.sum_nonneg (fun a _ => mul_nonneg (q.nonneg a) (mul_nonneg hv (hQ a)))
  have hpair := sqrt_pair_le hDnonneg hQnonneg
  have heq : 2 * ((∑ a, q.mass a * (v * D a)) + (∑ a, q.mass a * (v * Q a))) =
      2 * v * (∑ a, q.mass a * (D a + Q a)) := by
    rw [← Finset.sum_add_distrib]
    simp_rw [show ∀ a, q.mass a * (v * D a) + q.mass a * (v * Q a) =
      v * (q.mass a * (D a + Q a)) by intro; ring]
    rw [← Finset.mul_sum]
    ring
  rw [heq] at hpair
  have havgeq : (∑ a, q.mass a * (r * A a)) = r * ∑ a, q.mass a * A a := by
    simp_rw [show ∀ a, q.mass a * (r * A a) = r * (q.mass a * A a) by intro; ring]
    rw [Finset.mul_sum]
  have hrhseq : (∑ a, q.mass a * (2 * Real.sqrt (v * D a) +
      2 * Real.sqrt (v * Q a) + v * t a)) =
      2 * (∑ a, q.mass a * Real.sqrt (v * D a)) +
      2 * (∑ a, q.mass a * Real.sqrt (v * Q a)) +
      v * (∑ a, q.mass a * t a) := by
    simp_rw [mul_add]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    simp_rw [show ∀ a z, q.mass a * (2 * z) = 2 * (q.mass a * z) by intros; ring,
      show ∀ a, q.mass a * (v * t a) = v * (q.mass a * t a) by intro; ring]
    rw [← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]
  rw [havgeq, hrhseq] at havg
  linarith

end FiniteEntropy
