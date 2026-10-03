module

public import HittingTimeLooseHamilton.HostBatchVarianceMain
public import HittingTimeLooseHamilton.CompletionChebyshev
public import HittingTimeLooseHamilton.FrameSurvivalRatios

public section

/-! Relative concentration for actual uniform deletion from an arbitrary finite host. -/
noncomputable section
namespace LooseHamilton.FrameSurvival
open Finset
open scoped BigOperators
variable {α : Type*} [DecidableEq α]

theorem host_chebyshev_probability {H : Finset α} {k τ : ℕ}
    (F : Finset (Finset α)) (hFn : F.Nonempty)
    (hF : ∀ A ∈ F, A ⊆ H ∧ A.card=k)
    (hk4 : 4*k≤H.card) (ht4 : 4*τ≤H.card) {h : ℝ} (hh : 0<h) :
    (hostBatchLaw (show τ≤H.card by omega)).event
      (fun T => h < |(survivorCount F T.val : ℝ) /
        (zeta H.card τ k * F.card)-1|) ≤
      ((averageOverlap F/(k:ℝ))*Real.exp (4*(τ:ℝ)*k/H.card))/h^2 := by
  have hτ : τ≤H.card := by omega
  have hmean : 0<mean hτ F := mean_pos hτ F hF hFn (by omega)
  have hm : mean hτ F = zeta H.card τ k * F.card := by
    rw [mean_eq hτ F hF]
    unfold zeta
    ring
  have hc := (hostBatchLaw hτ).finite_relative_chebyshev_ratio
    (fun T => (survivorCount F T.val : ℝ)) hh hmean
  change (hostBatchLaw hτ).event
      (fun T => h < |(survivorCount F T.val : ℝ) / mean hτ F - 1|) ≤
        variance hτ F / (h^2 * (mean hτ F)^2) at hc
  rw [hm] at hc
  calc
    _ ≤ variance hτ F / (h^2 * (zeta H.card τ k * F.card)^2) := hc
    _ = (variance hτ F / (mean hτ F)^2) / h^2 := by rw [hm]; ring
    _ ≤ _ := div_le_div_of_nonneg_right (host_batch_variance_bound F hFn hF hk4 ht4)
      (sq_nonneg h)

end LooseHamilton.FrameSurvival
