module

public import HittingTimeLooseHamilton.KahnStatement
public import HittingTimeLooseHamilton.KahnTail

public section

/-!
# Analytic reduction of the random-order entropy estimate

This module separates the analytic estimates from the random-order entropy
estimate. `Kahn/Main.lean` proves `EntropyRevealBound` and applies this reduction
to obtain the unconditional theorem.
-/
open scoped BigOperators
noncomputable section
namespace Kahn
namespace MatchingLaw
variable {n r : ℕ} {H : Hypergraph n r}

/-- The unnormalised logarithmic penalty after the random-order count. -/
@[expose] def weightedPenalty (μ : FiniteEntropy.Law (MatchingIn H)) : ℝ :=
  ∑ v : Fin n, ∑ Y ∈ candidates (r := r) v, (marginal μ v).mass Y *
    ∑ i ∈ Finset.range (n / r),
      Real.log ((((i : ℝ) + 1) / (n / r : ℕ)) ^ (r - 1) + gamma μ v Y)

/-- An affine function of the collision moment can be summed using marginal normalisation. -/
lemma sum_affine_collision (μ : FiniteEntropy.Law (MatchingIn H)) (a b : ℝ) :
    (∑ v : Fin n, ∑ Y ∈ candidates (r := r) v,
      (marginal μ v).mass Y * (a + b *
        Real.rpow (gamma μ v Y) (1 / ((r : ℝ) - 1)))) =
    (n : ℝ) * a + b * errorSum μ := by
  classical
  have hrow (v : Fin n) :
      (∑ Y ∈ candidates (r := r) v, (marginal μ v).mass Y * (a + b *
        Real.rpow (gamma μ v Y) (1 / ((r : ℝ) - 1)))) =
      a + b * ∑ Y ∈ candidates (r := r) v, (marginal μ v).mass Y *
        Real.rpow (gamma μ v Y) (1 / ((r : ℝ) - 1)) := by
    calc
      _ = a * (∑ Y ∈ candidates (r := r) v, (marginal μ v).mass Y) +
          b * ∑ Y ∈ candidates (r := r) v, (marginal μ v).mass Y *
            Real.rpow (gamma μ v Y) (1 / ((r : ℝ) - 1)) := by
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro Y _
        ring
      _ = _ := by rw [candidates_mass_total, mul_one]
  simp_rw [hrow]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  simp [errorSum]

/-- Analytic bound on the entire penalty; no entropy/revelation claim is assumed. -/
lemma weightedPenalty_le (μ : FiniteEntropy.Law (MatchingIn H))
    (hr : 3 ≤ r) (hm : 0 < n / r) :
    weightedPenalty μ ≤
      (n : ℝ) * (-((r : ℝ) - 1) * (n / r : ℕ) +
        ((r : ℝ) - 1) * (1 + Real.log (n / r : ℕ)) + 2 * ((r : ℝ) + 1)) +
      (2 * ((r : ℝ) + 1) * (n / r : ℕ)) * errorSum μ := by
  classical
  let a : ℝ := -((r : ℝ) - 1) * (n / r : ℕ) +
    ((r : ℝ) - 1) * (1 + Real.log (n / r : ℕ)) + 2 * ((r : ℝ) + 1)
  let b : ℝ := 2 * ((r : ℝ) + 1) * (n / r : ℕ)
  calc
    weightedPenalty μ ≤ ∑ v : Fin n, ∑ Y ∈ candidates (r := r) v,
        (marginal μ v).mass Y *
          (a + b * Real.rpow (gamma μ v Y) (1 / ((r : ℝ) - 1))) := by
      apply Finset.sum_le_sum
      intro v _
      apply Finset.sum_le_sum
      intro Y _
      apply mul_le_mul_of_nonneg_left _ ((marginal μ v).nonneg Y)
      have h := KahnEntropy.local_penalty_le hm (show 2 ≤ r - 1 by omega)
        (gamma_nonneg μ v Y)
      have hcast : ((r - 1 : ℕ) : ℝ) = (r : ℝ) - 1 := by
        simpa using (Nat.cast_sub (R := ℝ) (show 1 ≤ r by omega))
      rw [hcast] at h
      simp only [one_div]
      dsimp [a, b]
      nlinarith
    _ = _ := sum_affine_collision μ a b

/-- Finite bound, conditional on the entropy-revelation inequality for this law. -/
lemma entropy_bound_of_reveal (μ : FiniteEntropy.Law (MatchingIn H))
    (hr : 3 ≤ r) (hn : r ≤ n) (hdiv : r ∣ n)
    (h : FiniteEntropy.entropy μ.mass ≤
      (1 / (r : ℝ)) * marginalEntropySum μ + (1 / (n : ℝ)) * weightedPenalty μ) :
    FiniteEntropy.entropy μ.mass ≤
      (1 / (r : ℝ)) * marginalEntropySum μ - correction n r +
      (2 * ((r : ℝ) + 1) / r) * errorSum μ +
      ((r : ℝ) - 1) * (1 + Real.log (n / r : ℕ)) + 2 * ((r : ℝ) + 1) := by
  have hrp : (0 : ℝ) < r := by exact_mod_cast (show 0 < r by omega)
  have hnp : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hm : 0 < n / r := Nat.div_pos hn (by omega)
  have hnm : (n : ℝ) = (r : ℝ) * (n / r : ℕ) := by
    exact_mod_cast (Nat.mul_div_cancel' hdiv).symm
  have hp := mul_le_mul_of_nonneg_left (weightedPenalty_le μ hr hm)
    (show 0 ≤ 1 / (n : ℝ) by positivity)
  apply le_trans h
  apply le_trans (add_le_add_right hp _)
  apply le_of_eq
  unfold correction
  rw [hnm]
  field_simp [hrp.ne', (Nat.cast_pos.mpr hm).ne']
  <;> ring

end MatchingLaw

/-- The finite random-order entropy estimate, proved in `Kahn/Main.lean`. -/
@[expose] def EntropyRevealBound : Prop :=
  ∀ r : ℕ, 3 ≤ r → ∀ n : ℕ, r * r ≤ n → r ∣ n →
    ∀ (H : Hypergraph n r) (μ : FiniteEntropy.Law (MatchingIn H)),
      FiniteEntropy.entropy μ.mass ≤
        (1 / (r : ℝ)) * MatchingLaw.marginalEntropySum μ +
          (1 / (n : ℝ)) * MatchingLaw.weightedPenalty μ

/-- Analytic implication used in the proof of Theorem 4.2 in `Kahn/Main.lean`. -/
theorem theorem42_of_reveal_bound (h : EntropyRevealBound) : Theorem42 := by
  intro r hr
  have hrp : (0 : ℝ) < r := by exact_mod_cast (show 0 < r by omega)
  refine ⟨10 * (r : ℝ), 10 * (r : ℝ), by positivity, by positivity, max (r * r) (Nat.ceil (Real.exp 1) + 1), ?_⟩
  intro n hn hdiv H μ
  have hrp : (0 : ℝ) < r := by exact_mod_cast (show 0 < r by omega)
  have hr3 : (3 : ℝ) ≤ r := by exact_mod_cast hr
  have hnr2 : r * r ≤ n := le_trans (le_max_left _ _) hn
  have hnr : r ≤ n := by nlinarith
  have hn3 : 3 ≤ n := by omega
  have hnp : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hln : 1 < Real.log (n : ℝ) := by
    apply (Real.lt_log_iff_exp_lt hnp).mpr
    have hceil : Nat.ceil (Real.exp 1) < n := by
      have := le_trans (le_max_right (r * r) _) hn
      omega
    exact lt_of_le_of_lt (Nat.le_ceil (Real.exp 1)) (by exact_mod_cast hceil)
  have hm : 0 < n / r := Nat.div_pos hnr (by omega)
  have hlog : Real.log (n / r : ℕ) ≤ Real.log (n : ℝ) :=
    Real.log_le_log (Nat.cast_pos.mpr hm) (by exact_mod_cast Nat.div_le_self n r)
  have hbound := MatchingLaw.entropy_bound_of_reveal μ hr hnr hdiv (h r hr n hnr2 hdiv H μ)
  have hE := MatchingLaw.errorSum_nonneg μ
  have hc : 2 * ((r : ℝ) + 1) / r ≤ 10 * r := by
    apply (div_le_iff₀ hrp).mpr
    nlinarith
  have hcE := mul_le_mul_of_nonneg_right hc hE
  have hlog' := mul_le_mul_of_nonneg_left hlog (show 0 ≤ (r : ℝ) - 1 by linarith)
  have hrem : ((r : ℝ) - 1) * (1 + Real.log (n / r : ℕ)) +
      2 * ((r : ℝ) + 1) < (10 * (r : ℝ)) * Real.log (n : ℝ) := by
    have hprod := mul_lt_mul_of_pos_left hln hrp
    nlinarith
  linarith

end Kahn
