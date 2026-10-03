module

public import HittingTimeLooseHamilton.IndexedSurvivalMoments
public import HittingTimeLooseHamilton.VariableSurvivalRatio

public section

/-! Uniform mean bounds for labelled objects with variable-sized supports. -/
noncomputable section
namespace LooseHamilton.IndexedSurvival
open Finset FrameSurvival CandidateLogSurvival
open scoped BigOperators
variable {α ι : Type*} [DecidableEq α] [DecidableEq ι]

/-- The support-size interval gives a multiplicative bound with no loss at
zero overlap. Labels with identical supports are retained with multiplicity. -/
theorem interval_mean_bounds {H : Finset α} {k d τ : ℕ}
    (hm : 0 < H.card) (hk4 : 4*k ≤ H.card) (ht4 : 4*τ ≤ H.card)
    (F : Finset ι) (support : ι → Finset α)
    (hsub : ∀ i ∈ F, support i ⊆ H)
    (hsize : ∀ i ∈ F, k-d ≤ (support i).card ∧ (support i).card ≤ k) :
    (F.card : ℝ) * zeta H.card k τ ≤ mean (by omega : τ ≤ H.card) F support ∧
    mean (by omega : τ ≤ H.card) F support ≤
      Real.exp (2*(d:ℝ)*τ/H.card) * zeta H.card k τ * F.card := by
  have hb (i : ι) (hi : i ∈ F) :=
    variable_zeta_bounds H.card k (support i).card d τ hm hk4 ht4
      (hsize i hi).2 (hsize i hi).1
  have h := mean_bounds (by omega : τ ≤ H.card) F support hsub
    (zeta H.card k τ) (Real.exp (2*(d:ℝ)*τ/H.card) * zeta H.card k τ)
    (fun i hi => (hb i hi).1) (fun i hi => (hb i hi).2)
  constructor
  · exact h.1
  · simpa only [mul_comm (F.card : ℝ)] using h.2

end LooseHamilton.IndexedSurvival
