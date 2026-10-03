module

public import HittingTimeLooseHamilton.PrivateRootDensityAveraging

public section

/-! Ambient abnormal candidates and their private-coordinate fibers.
All counts use the ambient vertex type, including for frames obtained from a
residual base. No source count, entropy hypothesis, or host membership is needed
for this averaging step. -/
noncomputable section
namespace LooseHamilton.BootstrapPrivateAbnormalFibers
open Finset AuxiliaryFrame
variable {V : Type*} [Fintype V] [DecidableEq V]
attribute [local instance] Classical.propDecidable

/-- Every actual abnormal candidate has precisely `r-2` private coordinates. -/
theorem private_card {r : ℕ} {original : SimpleHypergraph V}
    (F : Frame r original) (H : SimpleHypergraph V) (α : ℝ)
    {a : Finset V × V × V} (ha : a ∈ frameAbnormalCandidates F H α) :
    a.1.card = r-2 :=
  ((mem_filter.mp (mem_filter.mp ha).1).2).1.private_card

/-- Candidate balance bounds the actual abnormal set at the ambient scale. -/
theorem abnormal_card_le {r : ℕ} (hr : 3 ≤ r)
    {original : SimpleHypergraph V} (F : Frame r original)
    (H : SimpleHypergraph V) (α : ℝ) (hα : 0 ≤ α)
    (hbalance : ¬ F.candidateBad H α) :
    ((frameAbnormalCandidates F H α).card : ℝ) ≤
      α * (Fintype.card V : ℝ)^r := by
  have hcan : (F.candidates.card : ℝ) ≤ (Fintype.card V : ℝ)^r := by
    exact_mod_cast frame_candidates_card_le_pow hr F
  exact (frameAbnormalCandidates_card_le F H α hbalance).trans
    (mul_le_mul_of_nonneg_left hcan hα)

/-- Exact incidence count: each abnormal candidate is counted once per private
vertex, hence exactly `r-2` times (once when `r=3`). -/
theorem fiber_incidence_eq {r : ℕ} {original : SimpleHypergraph V}
    (F : Frame r original) (H : SimpleHypergraph V) (α : ℝ) :
    (∑ t : V, (privateBadCandidateFiber (frameAbnormalCandidates F H α) t).card) =
      (r-2) * (frameAbnormalCandidates F H α).card := by
  simp only [privateBadCandidateFiber]
  simp_rw [card_eq_sum_ones, sum_filter]
  rw [sum_comm]
  calc
    _ = ∑ a ∈ frameAbnormalCandidates F H α, a.1.card := by
      apply sum_congr rfl
      intro a ha
      simp
    _ = ∑ _a ∈ frameAbnormalCandidates F H α, (r-2) := by
      apply sum_congr rfl
      intro a ha
      exact private_card F H α ha
    _ = _ := by simp [Nat.mul_comm]

/-- The explicit exceptional set consists of ambient targets with large fibers. -/
@[expose] def exceptionalTargets {r : ℕ} {original : SimpleHypergraph V}
    (F : Frame r original) (H : SimpleHypergraph V) (α : ℝ) : Finset V :=
  privateExceptionalTargets (frameAbnormalCandidates F H α)
    (Real.sqrt ((r-2 : ℕ)*α)) (Fintype.card V) r

/-- Square-root averaging bounds the number of exceptional ambient targets. -/
theorem exceptional_card_le {r : ℕ} (hr : 3 ≤ r)
    {original : SimpleHypergraph V} (F : Frame r original)
    (H : SimpleHypergraph V) (α : ℝ) (hα : 0 < α)
    (hbalance : ¬ F.candidateBad H α) (hN : 0 < Fintype.card V) :
    ((exceptionalTargets F H α).card : ℝ) ≤
      Real.sqrt ((r-2 : ℕ)*α) * (Fintype.card V : ℝ) := by
  apply private_candidate_target_averaging hr _ α _ hα
  · exact_mod_cast hN
  · intro a ha
    exact (private_card F H α ha).le
  · exact abnormal_card_le hr F H α hα.le hbalance

/-- Outside the explicit exceptional set every ambient fiber has the required
bound, without any further restrictions on the target. -/
theorem fiber_card_le_of_not_exceptional {r : ℕ}
    {original : SimpleHypergraph V} (F : Frame r original)
    (H : SimpleHypergraph V) (α : ℝ) (t : V)
    (ht : t ∉ exceptionalTargets F H α) :
    ((privateBadCandidateFiber (frameAbnormalCandidates F H α) t).card : ℝ) ≤
      Real.sqrt ((r-2 : ℕ)*α) * (Fintype.card V : ℝ)^(r-1) := by
  simpa only [exceptionalTargets, privateExceptionalTargets, mem_filter,
    mem_univ, true_and, not_lt] using ht

/-- Balance provides one ambient exceptional set and simultaneous fiber bounds. -/
theorem exists_small_fibers {r : ℕ} (hr : 3 ≤ r)
    {original : SimpleHypergraph V} (F : Frame r original)
    (H : SimpleHypergraph V) (α : ℝ) (hα : 0 < α)
    (hbalance : ¬ F.candidateBad H α) (hN : 0 < Fintype.card V) :
    ∃ E : Finset V,
      (E.card : ℝ) ≤ Real.sqrt ((r-2 : ℕ)*α) * (Fintype.card V : ℝ) ∧
      ∀ t : V, t ∉ E →
        ((privateBadCandidateFiber (frameAbnormalCandidates F H α) t).card : ℝ) ≤
          Real.sqrt ((r-2 : ℕ)*α) * (Fintype.card V : ℝ)^(r-1) :=
  ⟨exceptionalTargets F H α, exceptional_card_le hr F H α hα hbalance hN,
    fun t ht => fiber_card_le_of_not_exceptional F H α t ht⟩

end LooseHamilton.BootstrapPrivateAbnormalFibers
