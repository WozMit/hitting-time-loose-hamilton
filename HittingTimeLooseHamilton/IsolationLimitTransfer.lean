module

public import HittingTimeLooseHamilton.IsolatedVertexExponentialBounds

public section

/-! Transferring scalar exponential estimates to actual stopping-time probabilities.
The hypotheses here are numerical limits, not probability conclusions. -/
noncomputable section
namespace LooseHamilton
open Filter
open scoped Topology

/-- The exact second-moment estimate converts its two scalar limits into early
stopping probability tending to zero. -/
theorem tauOne_early_probability_tendsto {r : ℕ} (hr : 2 ≤ r) (m : ℕ → ℕ)
    (hgap : ∀ᶠ n in atTop, m n + (n-1).choose (r-1) < n.choose r)
    (hfirst : Tendsto (fun n => Real.exp (isolationLowerExponent (Fin n) r (m n))/(n : ℝ)) atTop (𝓝 0))
    (hpair : Tendsto (fun n => 2*isolationLowerExponent (Fin n) r (m n) -
      isolationPairExponent (Fin n) r (m n)) atTop (𝓝 0)) :
    Tendsto (fun n => (processLaw (Fin n) r).event
      (fun σ => tauOne σ ≤ (m n : WithTop ℕ))) atTop (𝓝 0) := by
  have he := Real.continuous_exp.continuousAt.tendsto.comp hpair
  have hupper : Tendsto (fun n => Real.exp (isolationLowerExponent (Fin n) r (m n))/(n : ℝ) +
      Real.exp (2*isolationLowerExponent (Fin n) r (m n) -
        isolationPairExponent (Fin n) r (m n)) - 1) atTop (𝓝 0) := by
    simpa using (hfirst.add he).sub_const 1
  apply squeeze_zero' (Eventually.of_forall (fun n => (processLaw (Fin n) r).event_nonneg _)) ?_ hupper
  filter_upwards [hgap,eventually_ge_atTop 2] with n hg hn
  simpa only [Fintype.card_fin] using tauOne_early_probability_le_exp (V := Fin n) hr (by simpa using hn) (m n) (by simpa using hg)

/-- The first-moment estimate converts its scalar limit into late stopping
probability tending to zero. -/
theorem tauOne_late_probability_tendsto {r : ℕ} (hr : 1 ≤ r) (m : ℕ → ℕ)
    (hm : ∀ᶠ n in atTop, m n ≤ n.choose r)
    (hbound : Tendsto (fun n : ℕ => (n : ℝ) * Real.exp (-(((n-1).choose (r-1) : ℝ) * m n /
      (n.choose r : ℝ)))) atTop (𝓝 0)) :
    Tendsto (fun n => (processLaw (Fin n) r).event
      (fun σ => (m n : WithTop ℕ) < tauOne σ)) atTop (𝓝 0) := by
  apply squeeze_zero' (Eventually.of_forall (fun n => (processLaw (Fin n) r).event_nonneg _)) ?_ hbound
  filter_upwards [hm,eventually_ge_atTop r] with n hm hn
  have hN : 0 < n.choose r := Nat.choose_pos hn
  simpa only [Fintype.card_fin] using tauOne_late_probability_le_exp (V := Fin n) hr (m n)
    (by simpa only [completeEdges_card,Fintype.card_fin] using hm) (by simpa using hN)
end LooseHamilton
