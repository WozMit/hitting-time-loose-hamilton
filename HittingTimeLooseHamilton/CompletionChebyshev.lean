module

public import HittingTimeLooseHamilton.FiniteMomentBounds
public import HittingTimeLooseHamilton.BatchVarianceMain

public section

/-! Finite relative Chebyshev bounds for the actual uniform deletion experiment. -/
noncomputable section
open scoped BigOperators
namespace FiniteEntropy.Law
variable {Ω : Type*} [Fintype Ω]

/-- Chebyshev's inequality in relative centered form. -/
theorem finite_relative_chebyshev (p : FiniteEntropy.Law Ω) (X : Ω → ℝ)
    {h : ℝ} (hh : 0 < h) (hmean : 0 < p.finiteMean X) :
    p.event (fun ω => h * p.finiteMean X < |X ω - p.finiteMean X|) ≤
      p.finiteMean (fun ω => (X ω - p.finiteMean X)^2) /
        (h^2 * (p.finiteMean X)^2) := by
  have hp : 0 < h * p.finiteMean X := mul_pos hh hmean
  have hm := p.finite_markov (fun ω => sq_nonneg (X ω - p.finiteMean X))
    (sq_pos_of_pos hp)
  have he : p.event (fun ω => h * p.finiteMean X < |X ω - p.finiteMean X|) ≤
      p.event (fun ω => (h * p.finiteMean X)^2 ≤ (X ω - p.finiteMean X)^2) := by
    apply p.event_mono
    intro ω hω
    have ha := abs_nonneg (X ω - p.finiteMean X)
    have hs := sq_abs (X ω - p.finiteMean X)
    nlinarith
  simpa only [mul_pow] using he.trans hm

lemma relative_deviation_iff {x μ h : ℝ} (hμ : 0 < μ) :
    h < |x / μ - 1| ↔ h * μ < |x - μ| := by
  rw [show x / μ - 1 = (x - μ) / μ by field_simp,
    abs_div, abs_of_pos hμ, lt_div_iff₀ hμ]

theorem finite_relative_chebyshev_ratio (p : FiniteEntropy.Law Ω) (X : Ω → ℝ)
    {h : ℝ} (hh : 0 < h) (hmean : 0 < p.finiteMean X) :
    p.event (fun ω => h < |X ω / p.finiteMean X - 1|) ≤
      p.finiteMean (fun ω => (X ω - p.finiteMean X)^2) /
        (h^2 * (p.finiteMean X)^2) := by
  simpa only [relative_deviation_iff hmean] using p.finite_relative_chebyshev X hh hmean
end FiniteEntropy.Law

namespace LooseHamilton.BatchVariance

/-- The relative survivor deviation bound obtained from Lemma 7.1. -/
theorem batch_relative_chebyshev {m k τ : ℕ} (F : Finset (Finset (Fin m)))
    (hFn : F.Nonempty) (hF : ∀ A ∈ F, A.card = k)
    (hk4 : 4*k ≤ m) (ht4 : 4*τ ≤ m) {h : ℝ} (hh : 0 < h) :
    (batchLaw (show τ ≤ m by omega)).event
      (fun T => h * mean (show τ ≤ m by omega) F <
        |(survivors F T : ℝ) - mean (show τ ≤ m by omega) F|) ≤
      (averageOverlap F / (k:ℝ)) * Real.exp (4*(τ:ℝ)*k/m) / h^2 := by
  have hτ : τ ≤ m := by omega
  have hp := mean_pos hτ F hF hFn (by omega : τ ≤ m-k)
  have hc := (batchLaw hτ).finite_relative_chebyshev
    (fun T => (survivors F T : ℝ)) hh hp
  change (batchLaw hτ).event _ ≤ variance hτ F / (h^2 * (mean hτ F)^2) at hc
  have hb := div_le_div_of_nonneg_right (batch_variance_bound F hFn hF hk4 ht4)
    (sq_nonneg h)
  have he : variance hτ F / (h^2 * (mean hτ F)^2) =
      (variance hτ F / (mean hτ F)^2) / h^2 := by ring
  exact hc.trans (he ▸ hb)

/-- The exact center is the family size times its hypergeometric survival probability. -/
theorem batch_relative_chebyshev_center {m k τ : ℕ} (F : Finset (Finset (Fin m)))
    (hFn : F.Nonempty) (hF : ∀ A ∈ F, A.card = k)
    (hk4 : 4*k ≤ m) (ht4 : 4*τ ≤ m) {h : ℝ} (hh : 0 < h) :
    (batchLaw (show τ ≤ m by omega)).event
      (fun T => h * (((m-k).choose τ : ℝ) / (m.choose τ : ℝ) * F.card) <
        |(survivors F T : ℝ) -
          ((m-k).choose τ : ℝ) / (m.choose τ : ℝ) * F.card|) ≤
      (averageOverlap F / (k:ℝ)) * Real.exp (4*(τ:ℝ)*k/m) / h^2 := by
  have he : mean (show τ ≤ m by omega) F =
      ((m-k).choose τ : ℝ) / (m.choose τ : ℝ) * F.card := by
    rw [mean_eq (show τ ≤ m by omega) F hF]
    ring
  simpa only [he] using batch_relative_chebyshev F hFn hF hk4 ht4 hh
end LooseHamilton.BatchVariance
