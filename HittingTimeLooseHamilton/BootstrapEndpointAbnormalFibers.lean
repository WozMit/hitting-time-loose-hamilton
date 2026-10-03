module

public import HittingTimeLooseHamilton.BootstrapPrivateAbnormalFibers
public import HittingTimeLooseHamilton.EndpointBadRootCounting

public section

/-! Endpoint-coordinate averaging counts each actual abnormal candidate once. -/
noncomputable section
namespace LooseHamilton.BootstrapEndpointAbnormalFibers
open Finset AuxiliaryFrame
variable {V : Type*} [Fintype V] [DecidableEq V]
attribute [local instance] Classical.propDecidable

theorem fiber_incidence_eq (bad : Finset (Finset V × V × V)) :
    (∑ t : V, (endpointBadCandidateFiber bad t).card) = bad.card := by
  simp only [endpointBadCandidateFiber]
  simp_rw [card_eq_sum_ones, sum_filter]
  rw [sum_comm]
  simp

@[expose] def exceptionalTargets {r : ℕ} {original : SimpleHypergraph V}
    (F : Frame r original) (H : SimpleHypergraph V) (α : ℝ) : Finset V :=
  univ.filter fun t => Real.sqrt α * (Fintype.card V : ℝ)^(r-1) <
    (endpointBadCandidateFiber (frameAbnormalCandidates F H α) t).card

theorem exceptional_card_le {r : ℕ} (hr : 3 ≤ r)
    {original : SimpleHypergraph V} (F : Frame r original)
    (H : SimpleHypergraph V) (α : ℝ) (hα : 0 < α)
    (hbalance : ¬ F.candidateBad H α) (hN : 0 < Fintype.card V) :
    ((exceptionalTargets F H α).card : ℝ) ≤ Real.sqrt α * (Fintype.card V : ℝ) := by
  have hs : (∑ t : V, ((endpointBadCandidateFiber (frameAbnormalCandidates F H α) t).card : ℝ)) =
      ((frameAbnormalCandidates F H α).card : ℝ) := by
    exact_mod_cast fiber_incidence_eq (frameAbnormalCandidates F H α)
  apply Migration.coordinate_exceptional_targets univ
    (fun t => (endpointBadCandidateFiber (frameAbnormalCandidates F H α) t).card)
    (Real.sqrt α) (Fintype.card V) (r-1)
    (fun _ _ => Nat.cast_nonneg _) (Real.sqrt_pos.2 hα) (by exact_mod_cast hN)
  rw [Real.sq_sqrt hα.le, show r-1+1=r by omega, hs]
  exact BootstrapPrivateAbnormalFibers.abnormal_card_le hr F H α hα.le hbalance

theorem fiber_card_le_of_not_exceptional {r : ℕ}
    {original : SimpleHypergraph V} (F : Frame r original)
    (H : SimpleHypergraph V) (α : ℝ) (t : V)
    (ht : t ∉ exceptionalTargets F H α) :
    ((endpointBadCandidateFiber (frameAbnormalCandidates F H α) t).card : ℝ) ≤
      Real.sqrt α * (Fintype.card V : ℝ)^(r-1) := by
  simpa only [exceptionalTargets, mem_filter, mem_univ, true_and, not_lt] using ht

end LooseHamilton.BootstrapEndpointAbnormalFibers
