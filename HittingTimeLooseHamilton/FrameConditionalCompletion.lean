module

public import HittingTimeLooseHamilton.CandidateIndexedSurvival

public section

/-! The actual completion experiment conditional on deleting the candidate.
The fixed boundary edges are retained; only the unexposed host is sampled. -/
noncomputable section
namespace LooseHamilton.CandidateBalance
open Finset AuxiliaryFrame FrameSurvival
open scoped BigOperators
variable {V : Type} [Fintype V] [DecidableEq V]
variable {r : ℕ} {original : Finset (Finset V)}

/-- Candidate completions never use the candidate edge, including boundary edges. -/
theorem completion_support_candidate_absent (f : Frame r original) (hr : 3 ≤ r)
    (D : Finset V) (H : SimpleHypergraph V) (c : Finset V × V × V)
    (hc : f.LegalCandidate c) {E : SimpleHypergraph V}
    (hE : E ∈ f.completionFamily H c) :
    c.1 ∪ {c.2.1,c.2.2} ∉ E ∩ unexposed f D H :=
  fun h => f.candidate_absent hr hc hE (mem_inter.mp h).1

/-- The conditional sampling host is the unexposed host minus the candidate. -/
theorem completion_support_subset_erased (f : Frame r original) (hr : 3 ≤ r)
    (D : Finset V) (H : SimpleHypergraph V) (c : Finset V × V × V)
    (hc : f.LegalCandidate c) {E : SimpleHypergraph V}
    (hE : E ∈ f.completionFamily H c) :
    E ∩ unexposed f D H ⊆ (unexposed f D H).erase (c.1 ∪ {c.2.1,c.2.2}) :=
  subset_erase.mpr ⟨inter_subset_right, completion_support_candidate_absent f hr D H c hc hE⟩

/-- Deleting the distinguished candidate has no further effect on completion counts. -/
theorem completionCount_insert_candidate (f : Frame r original) (hr : 3 ≤ r)
    (H T : SimpleHypergraph V) (c : Finset V × V × V) (hc : f.LegalCandidate c) :
    f.completionCount (H \ insert (c.1 ∪ {c.2.1,c.2.2}) T) c =
      f.completionCount (H \ T) c := by
  rw [f.completionCount_delete, f.completionCount_delete]
  exact survivorCount_insert T (fun _ hE => f.candidate_absent hr hc hE)

/-- Exact labelled survival count under the smaller conditional uniform batch. -/
theorem completionCount_conditioned_eq_indexed (f : Frame r original) (hr : 3 ≤ r)
    (D : Finset V) (H T : SimpleHypergraph V) (c : Finset V × V × V)
    (hc : f.LegalCandidate c)
    (hT : T ⊆ (unexposed f D H).erase (c.1 ∪ {c.2.1,c.2.2})) :
    f.completionCount (H \ insert (c.1 ∪ {c.2.1,c.2.2}) T) c =
      IndexedSurvival.count (f.completionFamily H c)
        (fun E => E ∩ unexposed f D H) T := by
  rw [completionCount_insert_candidate f hr H T c hc]
  exact completionCount_eq_indexed f D H T c (hT.trans (erase_subset _ _))

/-- Conditional sampling is exactly uniform sampling of `τ-1` edges after erasing
its distinguished candidate; this event identity does not assume independence. -/
theorem completion_batch_conditioning (f : Frame r original)
    (D : Finset V) (H : SimpleHypergraph V) (c : Finset V × V × V)
    (he : c.1 ∪ {c.2.1,c.2.2} ∈ unexposed f D H)
    {τ : ℕ} (hτ : 1 ≤ τ) (hτH : τ ≤ (unexposed f D H).card)
    (P : SimpleHypergraph V → Prop) :
    (hostBatchLaw hτH).event (fun T => c.1 ∪ {c.2.1,c.2.2} ∈ T.val ∧ P T.val) =
      (hostBatchLaw hτH).event (fun T => c.1 ∪ {c.2.1,c.2.2} ∈ T.val) *
        (hostBatchLaw (show τ-1 ≤ ((unexposed f D H).erase
          (c.1 ∪ {c.2.1,c.2.2})).card by rw [card_erase_of_mem he]; omega)).event
          (fun T => P (insert (c.1 ∪ {c.2.1,c.2.2}) T.val)) :=
  candidate_conditioning he hτ hτH P

/-- The conditional remainder restores the retained allowed boundary edges. -/
theorem conditioned_rawRemainder_eq (f : Frame r original)
    (D : Finset V) (H T : SimpleHypergraph V) (c : Finset V × V × V)
    (he : c.1 ∪ {c.2.1,c.2.2} ∈ unexposed f D H)
    (hT : T ⊆ (unexposed f D H).erase (c.1 ∪ {c.2.1,c.2.2})) :
    rawRemainder f D H (insert (c.1 ∪ {c.2.1,c.2.2}) T) =
      f.rawHost (H \ insert (c.1 ∪ {c.2.1,c.2.2}) T) := by
  rw [rawRemainder_eq f D H _ (insert_subset he (hT.trans (erase_subset _ _)))]
  exact (f.rawHost_delete H _).symm

/-- On a nonempty source family the corrected conditional factor is precisely
`binom(m0-k,τ-1)/binom(m0-1,τ-1)`. -/
theorem conditioned_zeta_eq (m k τ : ℕ) (hk : 1 ≤ k) :
    CandidateLogSurvival.zeta (m-1) (k-1) (τ-1) = conditionedZeta m τ k := by
  unfold CandidateLogSurvival.zeta conditionedZeta
  rw [show m-1-(k-1) = m-k by omega]

/-- Actual conditional completion means, with the loss from retained boundary
edges bounded rather than silently removing those edges from the object. -/
theorem completion_conditioned_mean_bounds (f : Frame r original) (hr : 3 ≤ r)
    (D : Finset V) (H : SimpleHypergraph V) (c : Finset V × V × V)
    (hmain : (f.cycleFamily H).Nonempty) (hc : f.LegalCandidate c)
    (he : c.1 ∪ {c.2.1,c.2.2} ∈ unexposed f D H) {τ : ℕ}
    (hm : 0 < (unexposed f D H).card-1)
    (hk4 : 4*(f.k-1) ≤ (unexposed f D H).card-1)
    (ht4 : 4*(τ-1) ≤ (unexposed f D H).card-1) :
    (f.completionCount H c : ℝ) * conditionedZeta (unexposed f D H).card τ f.k ≤
      IndexedSurvival.mean (show τ-1 ≤ ((unexposed f D H).erase
        (c.1 ∪ {c.2.1,c.2.2})).card by rw [card_erase_of_mem he]; omega)
        (f.completionFamily H c) (fun E => E ∩ unexposed f D H) ∧
    IndexedSurvival.mean (show τ-1 ≤ ((unexposed f D H).erase
        (c.1 ∪ {c.2.1,c.2.2})).card by rw [card_erase_of_mem he]; omega)
        (f.completionFamily H c) (fun E => E ∩ unexposed f D H) ≤
      Real.exp (2*((2*D.card:ℕ):ℝ)*(τ-1:ℕ)/((unexposed f D H).card-1:ℕ)) *
        conditionedZeta (unexposed f D H).card τ f.k * f.completionCount H c := by
  have h := IndexedSurvival.interval_mean_bounds
    (H := (unexposed f D H).erase (c.1 ∪ {c.2.1,c.2.2}))
    (by simpa only [card_erase_of_mem he] using hm)
    (by simpa only [card_erase_of_mem he] using hk4)
    (by simpa only [card_erase_of_mem he] using ht4)
    (f.completionFamily H c) (fun E => E ∩ unexposed f D H)
    (fun _ hE => completion_support_subset_erased f hr D H c hc hE)
    (fun E hE => completion_restricted_support_card f hr D H E hmain c hc hE)
  simpa only [card_erase_of_mem he, conditioned_zeta_eq _ _ _ (f.k_pos hr hmain),
    Frame.completionCount] using h

end LooseHamilton.CandidateBalance
