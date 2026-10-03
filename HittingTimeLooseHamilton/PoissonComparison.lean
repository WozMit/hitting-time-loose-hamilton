module

public import Mathlib.Probability.Distributions.Poisson.Basic
public import Mathlib.Tactic

public section

/-! Finite birth-rate domination by the Poisson distribution. -/
noncomputable section
namespace LooseHamilton
open Finset

/-- The unnormalised Poisson mass. This definition also covers mean zero. -/
@[expose] def poissonWeight (μ : ℝ) (q : ℕ) : ℝ := μ ^ q / (q.factorial : ℝ)

lemma poissonWeight_nonneg {μ : ℝ} (hμ : 0 ≤ μ) (q : ℕ) :
    0 ≤ poissonWeight μ q := by
  unfold poissonWeight
  positivity

lemma poissonWeight_succ (μ : ℝ) (q : ℕ) :
    (q + 1 : ℝ) * poissonWeight μ (q + 1) = μ * poissonWeight μ q := by
  unfold poissonWeight
  rw [pow_succ, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  have hf : (q.factorial : ℝ) ≠ 0 := by positivity
  have hq : (q : ℝ) + 1 ≠ 0 := by positivity
  field_simp <;> ring

/-- A birth-rate inequality implies a monotone likelihood ratio, without
requiring positive probabilities or a positive Poisson mean. -/
lemma poissonWeight_cross {p : ℕ → ℝ} {μ : ℝ} (hμ : 0 ≤ μ)
    (hrec : ∀ q : ℕ, (q + 1 : ℝ) * p (q + 1) ≤ μ * p q)
    {i j : ℕ} (hij : i ≤ j) :
    p j * poissonWeight μ i ≤ p i * poissonWeight μ j := by
  induction j, hij using Nat.le_induction with
  | base => exact le_rfl
  | succ j hij ih =>
    have h₁ := mul_le_mul_of_nonneg_right (hrec j) (poissonWeight_nonneg hμ i)
    have h₂ := mul_le_mul_of_nonneg_left ih hμ
    have hw := poissonWeight_succ μ j
    have hpos : (0 : ℝ) < j + 1 := by positivity
    apply (mul_le_mul_iff_right₀ hpos).mp
    calc
      (j + 1 : ℝ) * (p (j + 1) * poissonWeight μ i) =
          ((j + 1 : ℝ) * p (j + 1)) * poissonWeight μ i := by ring
      _ ≤ (μ * p j) * poissonWeight μ i := h₁
      _ = μ * (p j * poissonWeight μ i) := by ring
      _ ≤ μ * (p i * poissonWeight μ j) := h₂
      _ = p i * ((j + 1 : ℝ) * poissonWeight μ (j + 1)) := by rw [hw]; ring
      _ = (j + 1 : ℝ) * (p i * poissonWeight μ (j + 1)) := by ring

/-- The finite double-sum form of monotone likelihood-ratio comparison. -/
lemma finite_prefix_weight_comparison (p w : ℕ → ℝ) (K k : ℕ)
    (hk : k ≤ K + 1)
    (hnorm : ∑ q ∈ range (K + 1), p q = 1)
    (hcross : ∀ i j : ℕ, i ≤ j → p j * w i ≤ p i * w j) :
    ∑ i ∈ range k, w i ≤
      (∑ i ∈ range k, p i) * (∑ i ∈ range (K + 1), w i) := by
  have hsub : range k ⊆ range (K + 1) := range_mono hk
  have hp := sum_sdiff (f := p) hsub
  have hw := sum_sdiff (f := w) hsub
  have hdouble :
      (∑ i ∈ range k, w i) * (∑ j ∈ range (K + 1) \ range k, p j) ≤
      (∑ i ∈ range k, p i) * (∑ j ∈ range (K + 1) \ range k, w j) := by
    rw [sum_mul, sum_mul]
    apply sum_le_sum
    intro i hi
    rw [mul_sum, mul_sum]
    apply sum_le_sum
    intro j hj
    have hi' := mem_range.mp hi
    have hj' : k ≤ j := Nat.le_of_not_lt (by simpa using (mem_sdiff.mp hj).2)
    simpa only [mul_comm] using hcross i j (by omega)
  rw [hnorm] at hp
  calc
    (∑ i ∈ range k, w i) =
        (∑ i ∈ range k, w i) *
          ((∑ j ∈ range (K + 1) \ range k, p j) + (∑ i ∈ range k, p i)) := by rw [hp]; ring
    _ ≤ (∑ i ∈ range k, p i) * (∑ j ∈ range (K + 1) \ range k, w j) +
          (∑ i ∈ range k, w i) * (∑ i ∈ range k, p i) := by nlinarith [hdouble]
    _ = (∑ i ∈ range k, p i) * (∑ i ∈ range (K + 1), w i) := by rw [← hw]; ring

/-- A finite nonnegative mass distribution whose upward birth rates are at most
`μ` has every upper tail bounded by the corresponding Poisson upper tail.
The right side is written as one minus a finite Poisson cumulative sum, so the
statement is meaningful without any infinite-sum conventions. -/
theorem finite_poisson_tail_le (p : ℕ → ℝ) (μ : ℝ) (K k : ℕ)
    (hμ : 0 ≤ μ) (hp : ∀ q : ℕ, 0 ≤ p q)
    (hnorm : ∑ q ∈ range (K + 1), p q = 1)
    (hrec : ∀ q : ℕ, (q + 1 : ℝ) * p (q + 1) ≤ μ * p q) :
    (∑ q ∈ (range (K + 1)).filter (fun q => k ≤ q), p q) ≤
      1 - Real.exp (-μ) * (∑ q ∈ range k, μ ^ q / (q.factorial : ℝ)) := by
  have hexp := Real.sum_le_exp_of_nonneg hμ k
  have hexppos := Real.exp_pos μ
  by_cases hk : k ≤ K + 1
  · have hcomp := finite_prefix_weight_comparison p (poissonWeight μ) K k hk hnorm
      (fun i j hij => poissonWeight_cross hμ hrec hij)
    have hpref : 0 ≤ ∑ q ∈ range k, p q := sum_nonneg (fun q _ => hp q)
    have htotal := Real.sum_le_exp_of_nonneg hμ (K + 1)
    change (∑ q ∈ range (K + 1), poissonWeight μ q) ≤ Real.exp μ at htotal
    have hcomp' : (∑ q ∈ range k, poissonWeight μ q) ≤
        (∑ q ∈ range k, p q) * Real.exp μ :=
      hcomp.trans (mul_le_mul_of_nonneg_left htotal hpref)
    have hcdf : Real.exp (-μ) * (∑ q ∈ range k, μ ^ q / (q.factorial : ℝ)) ≤
        ∑ q ∈ range k, p q := by
      rw [Real.exp_neg, inv_mul_eq_div]
      exact (div_le_iff₀ hexppos).mpr hcomp'
    have hset : (range (K + 1)).filter (fun q => k ≤ q) = range (K + 1) \ range k := by
      ext q
      simp only [mem_filter, mem_range, mem_sdiff]
      omega
    rw [hset]
    have hsplit := sum_sdiff (f := p) (range_mono hk)
    rw [hnorm] at hsplit
    linarith
  · have hset : (range (K + 1)).filter (fun q => k ≤ q) = ∅ := by
      ext q
      simp only [mem_filter, mem_range, notMem_empty, iff_false]
      omega
    rw [hset, sum_empty]
    have hbound : Real.exp (-μ) * (∑ q ∈ range k, μ ^ q / (q.factorial : ℝ)) ≤ 1 := by
      rw [Real.exp_neg, inv_mul_eq_div]
      exact (div_le_iff₀ hexppos).mpr (by simpa using hexp)
    linarith

/-- The equivalent lower-tail formulation, allowing thresholds beyond the
finite support. -/
theorem finite_poisson_cdf_le (p : ℕ → ℝ) (μ : ℝ) (K k : ℕ)
    (hμ : 0 ≤ μ) (hp : ∀ q : ℕ, 0 ≤ p q)
    (hsupport : ∀ q : ℕ, K < q → p q = 0)
    (hnorm : ∑ q ∈ range (K + 1), p q = 1)
    (hrec : ∀ q : ℕ, (q + 1 : ℝ) * p (q + 1) ≤ μ * p q) :
    Real.exp (-μ) * (∑ q ∈ range k, μ ^ q / (q.factorial : ℝ)) ≤
      ∑ q ∈ range k, p q := by
  by_cases hk : k ≤ K + 1
  · have ht := finite_poisson_tail_le p μ K k hμ hp hnorm hrec
    have hset : (range (K + 1)).filter (fun q => k ≤ q) = range (K + 1) \ range k := by
      ext q
      simp only [mem_filter, mem_range, mem_sdiff]
      omega
    rw [hset] at ht
    have hsplit := sum_sdiff (f := p) (range_mono hk)
    rw [hnorm] at hsplit
    linarith
  · have hsub : range (K + 1) ⊆ range k := range_mono (by omega)
    have heq : (∑ q ∈ range k, p q) = 1 := by
      rw [← hnorm]
      symm
      apply sum_subset hsub
      intro q hq hq'
      exact hsupport q (by simp only [mem_range] at hq'; omega)
    rw [heq, Real.exp_neg, inv_mul_eq_div]
    exact (div_le_iff₀ (Real.exp_pos μ)).mpr (by simpa using Real.sum_le_exp_of_nonneg hμ k)

/-- The finite expression used above is exactly mathlib's Poisson cumulative
mass, including the zero-mean distribution. -/
lemma poisson_cdf_eq (μ : NNReal) (k : ℕ) :
    (∑ q ∈ range k, ProbabilityTheory.poissonPMFReal μ q) =
      Real.exp (-(μ : ℝ)) * (∑ q ∈ range k, (μ : ℝ) ^ q / (q.factorial : ℝ)) := by
  rw [mul_sum]
  apply sum_congr rfl
  intro q hq
  unfold ProbabilityTheory.poissonPMFReal
  ring

/-- Stochastic domination in terms of mathlib's actual Poisson mass function. -/
theorem finite_poisson_cdf_le_pmf (p : ℕ → ℝ) (μ : NNReal) (K k : ℕ)
    (hp : ∀ q : ℕ, 0 ≤ p q)
    (hsupport : ∀ q : ℕ, K < q → p q = 0)
    (hnorm : ∑ q ∈ range (K + 1), p q = 1)
    (hrec : ∀ q : ℕ, (q + 1 : ℝ) * p (q + 1) ≤ (μ : ℝ) * p q) :
    (∑ q ∈ range k, ProbabilityTheory.poissonPMFReal μ q) ≤
      ∑ q ∈ range k, p q := by
  rw [poisson_cdf_eq]
  exact finite_poisson_cdf_le p μ K k μ.coe_nonneg hp hsupport hnorm hrec

end LooseHamilton
