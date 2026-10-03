module

public import HittingTimeLooseHamilton.FrameRestrictedSupports
public import HittingTimeLooseHamilton.IndexedSurvivalOverlapLaw
public import HittingTimeLooseHamilton.FrameSurvivalAuxiliary

public section

/-! Actual directed frame cycle and completion counts under restricted sampling.
The labels are the original edge families; only their sampled supports shrink. -/
noncomputable section
namespace LooseHamilton.CandidateBalance
open Finset AuxiliaryFrame CandidateLogSurvival
variable {V : Type} [Fintype V] [DecidableEq V]
variable {r : ℕ} {original : Finset (Finset V)}

/-- Exact actual cycle count, including the prescribed frame directions. -/
theorem cycleCount_eq_indexed (f : Frame r original) (D : Finset V)
    (H T : SimpleHypergraph V) (hT : T ⊆ unexposed f D H) :
    f.cycleCount (H \ T) = IndexedSurvival.count (f.cycleFamily H)
      (fun E => E ∩ unexposed f D H) T := by
  rw [f.cycleCount_delete]
  unfold FrameSurvival.survivorCount IndexedSurvival.count
  congr 1
  apply filter_congr
  intro E _
  exact ⟨fun h => (disjoint_restricted_support_iff E _ T hT).mpr h.symm |>.symm,
    fun h => (disjoint_restricted_support_iff E _ T hT).mp h.symm |>.symm⟩

/-- Exact actual completion count, with the original candidate orientations. -/
theorem completionCount_eq_indexed (f : Frame r original) (D : Finset V)
    (H T : SimpleHypergraph V) (c : Finset V × V × V)
    (hT : T ⊆ unexposed f D H) :
    f.completionCount (H \ T) c = IndexedSurvival.count (f.completionFamily H c)
      (fun E => E ∩ unexposed f D H) T := by
  rw [f.completionCount_delete]
  unfold FrameSurvival.survivorCount IndexedSurvival.count
  congr 1
  apply filter_congr
  intro E _
  exact ⟨fun h => (disjoint_restricted_support_iff E _ T hT).mpr h.symm |>.symm,
    fun h => (disjoint_restricted_support_iff E _ T hT).mp h.symm |>.symm⟩

theorem cycle_restricted_mean_bounds (f : Frame r original) (hr : 3 ≤ r)
    (D : Finset V) (H : SimpleHypergraph V) {τ : ℕ}
    (hm : 0 < (unexposed f D H).card)
    (hk4 : 4*f.k ≤ (unexposed f D H).card) (ht4 : 4*τ ≤ (unexposed f D H).card) :
    (f.cycleCount H : ℝ) * zeta (unexposed f D H).card f.k τ ≤
      IndexedSurvival.mean (by omega : τ ≤ (unexposed f D H).card)
        (f.cycleFamily H) (fun E => E ∩ unexposed f D H) ∧
    IndexedSurvival.mean (by omega : τ ≤ (unexposed f D H).card)
        (f.cycleFamily H) (fun E => E ∩ unexposed f D H) ≤
      Real.exp (2*((2*D.card:ℕ):ℝ)*τ/(unexposed f D H).card) *
        zeta (unexposed f D H).card f.k τ * f.cycleCount H := by
  exact IndexedSurvival.interval_mean_bounds hm hk4 ht4 _ _
    (fun _ _ => inter_subset_right) (fun E hE => cycle_restricted_support_card f hr D H E hE)

theorem completion_restricted_mean_bounds (f : Frame r original) (hr : 3 ≤ r)
    (D : Finset V) (H : SimpleHypergraph V) (c : Finset V × V × V)
    (hmain : (f.cycleFamily H).Nonempty) (hc : f.LegalCandidate c) {τ : ℕ}
    (hm : 0 < (unexposed f D H).card)
    (hk4 : 4*(f.k-1) ≤ (unexposed f D H).card) (ht4 : 4*τ ≤ (unexposed f D H).card) :
    (f.completionCount H c : ℝ) * zeta (unexposed f D H).card (f.k-1) τ ≤
      IndexedSurvival.mean (by omega : τ ≤ (unexposed f D H).card)
        (f.completionFamily H c) (fun E => E ∩ unexposed f D H) ∧
    IndexedSurvival.mean (by omega : τ ≤ (unexposed f D H).card)
        (f.completionFamily H c) (fun E => E ∩ unexposed f D H) ≤
      Real.exp (2*((2*D.card:ℕ):ℝ)*τ/(unexposed f D H).card) *
        zeta (unexposed f D H).card (f.k-1) τ * f.completionCount H c := by
  exact IndexedSurvival.interval_mean_bounds hm hk4 ht4 _ _
    (fun _ _ => inter_subset_right)
    (fun E hE => completion_restricted_support_card f hr D H E hmain c hc hE)

theorem cycle_restricted_variance_bound (f : Frame r original) (hr : 3 ≤ r)
    (D : Finset V) (H : SimpleHypergraph V) (hmain : (f.cycleFamily H).Nonempty) {τ : ℕ}
    (hm : 0 < (unexposed f D H).card)
    (hk4 : 4*f.k ≤ (unexposed f D H).card) (ht4 : 4*τ ≤ (unexposed f D H).card) :
    IndexedSurvival.variance (by omega : τ ≤ (unexposed f D H).card)
        (f.cycleFamily H) (fun E => E ∩ unexposed f D H) /
      (IndexedSurvival.mean (by omega : τ ≤ (unexposed f D H).card)
        (f.cycleFamily H) (fun E => E ∩ unexposed f D H))^2 ≤
    Real.exp (4*((2*D.card:ℕ):ℝ)*τ/(unexposed f D H).card) *
      (Real.exp (4*(τ:ℝ)*f.k/(unexposed f D H).card)-1) *
      IndexedSurvival.uniformOverlap (f.cycleFamily H) (fun E => E ∩ unexposed f D H) / f.k := by
  exact IndexedSurvival.normalized_variance_bound hm (f.k_pos hr hmain) hk4 ht4 _ _ hmain
    (fun _ _ => inter_subset_right) (fun E hE => cycle_restricted_support_card f hr D H E hE)

theorem completion_restricted_variance_bound (f : Frame r original) (hr : 3 ≤ r)
    (D : Finset V) (H : SimpleHypergraph V) (c : Finset V × V × V)
    (hmain : (f.cycleFamily H).Nonempty) (hc : f.LegalCandidate c)
    (hcomp : (f.completionFamily H c).Nonempty) {τ : ℕ}
    (hm : 0 < (unexposed f D H).card) (hk : 0 < f.k-1)
    (hk4 : 4*(f.k-1) ≤ (unexposed f D H).card) (ht4 : 4*τ ≤ (unexposed f D H).card) :
    IndexedSurvival.variance (by omega : τ ≤ (unexposed f D H).card)
        (f.completionFamily H c) (fun E => E ∩ unexposed f D H) /
      (IndexedSurvival.mean (by omega : τ ≤ (unexposed f D H).card)
        (f.completionFamily H c) (fun E => E ∩ unexposed f D H))^2 ≤
    Real.exp (4*((2*D.card:ℕ):ℝ)*τ/(unexposed f D H).card) *
      (Real.exp (4*(τ:ℝ)*(f.k-1:ℕ)/(unexposed f D H).card)-1) *
      IndexedSurvival.uniformOverlap (f.completionFamily H c)
        (fun E => E ∩ unexposed f D H) / (f.k-1:ℕ) := by
  exact IndexedSurvival.normalized_variance_bound hm hk hk4 ht4 _ _ hcomp
    (fun _ _ => inter_subset_right)
    (fun E hE => completion_restricted_support_card f hr D H E hmain c hc hE)

end LooseHamilton.CandidateBalance
