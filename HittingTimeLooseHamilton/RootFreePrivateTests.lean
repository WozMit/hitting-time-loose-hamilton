module

public import HittingTimeLooseHamilton.RootFreeCountInvariance
public import HittingTimeLooseHamilton.PrivateMigrationCandidates

public section

/-! # Pre-registered private-coordinate root-link tests

Legality is checked in the singleton counterfactual host containing the proposed
root edge, never in the observed host. Counts and the source mean all delete the
root. Thus the test is constant on each root-free observation fiber, before any
root edge is sampled. A link is bad if every legal unordered split has a count
strictly below its prescribed source scale. Vacuous tests include all forbidden
and colliding labels.
-/
noncomputable section
namespace LooseHamilton
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Structural admissibility of a split of the proposed link `A`. The fixed
allowed universe is retained unchanged under marker modifications. -/
structure PrivateRootSplitLegal (r : ℕ) (markers allowed : Finset (Finset V))
    (S q : Finset V) (x t : V) (A R uv : Finset V) : Prop where
  rest_card : S.card = r-3
  link_card : A.card = r-1
  root_absent : x ∉ A
  edge_allowed : insert x A ∈ allowed
  source_legal : LegalPrivateCompletion r markers (insert x S) q
  target_legal : LegalPrivateCompletion r markers (insert t S) q
  split_legal : PrivateMigrationLegal r markers {insert x A} (insert t S) q x R uv

/-- Mean degree on the source vertex space, using the outer host. -/
@[expose] def privateRootSourceMean (r : ℕ) (outer : Finset (Finset V)) (S : Finset V)
    (x : V) : ℝ :=
  (r : ℝ) * (inducedHost (univ \ insert x S) outer).card /
    (univ \ insert x S).card

/-- Actual root-free private-move badness, registered for arbitrary raw labels. -/
@[expose] def PrivateRootBad (r : ℕ) (markers allowed inner outer : Finset (Finset V))
    (S q : Finset V) (x t : V) (c : ℝ) (A : Finset V) : Prop :=
  ∀ R uv, PrivateRootSplitLegal r markers allowed S q x t A R uv →
    (privateMigrationSummand r markers inner (insert t S) q x (R,uv) : ℝ) <
      c * (completionCount r markers inner (insert x S) q : ℝ) /
        privateRootSourceMean r outer S x

/-- The full potential link test, independent of which root edges are present. -/
@[expose] def privateRootBadSet (r : ℕ) (markers allowed inner outer : Finset (Finset V))
    (S q : Finset V) (x t : V) (c : ℝ) : Finset (Finset V) := by
  classical
  exact (univ.powersetCard (r-1)).filter
    (fun A => PrivateRootBad r markers allowed inner outer S q x t c A)

theorem privateRootSourceMean_rootFreeEdges (r : ℕ) (outer : Finset (Finset V))
    (S : Finset V) (x : V) :
    privateRootSourceMean r (rootFreeEdges x outer) S x =
      privateRootSourceMean r outer S x := by
  unfold privateRootSourceMean
  rw [inducedHost_rootFreeEdges _ outer x (by simp)]

theorem privateMigrationSummand_rootFreeEdges (r : ℕ)
    (markers inner : Finset (Finset V)) (D q : Finset V) (x : V)
    (a : Finset V × Finset V) :
    privateMigrationSummand r markers (rootFreeEdges x inner) D q x a =
      privateMigrationSummand r markers inner D q x a := by
  unfold privateMigrationSummand
  rw [inducedHost_rootFreeEdges _ inner x (by simp)]

/-- Literal invariance after erasing both inner and outer root links. -/
theorem privateRootBad_rootFreeEdges (r : ℕ)
    (markers allowed inner outer : Finset (Finset V))
    (S q : Finset V) (x t : V) (c : ℝ) (A : Finset V) :
    PrivateRootBad r markers allowed (rootFreeEdges x inner) (rootFreeEdges x outer)
      S q x t c A ↔ PrivateRootBad r markers allowed inner outer S q x t c A := by
  unfold PrivateRootBad
  simp only [privateMigrationSummand_rootFreeEdges, privateRootSourceMean_rootFreeEdges,
    completionCount_rootFreeEdges r markers inner (insert x S) q x (mem_insert_self _ _)]

theorem privateRootBadSet_rootFreeEdges (r : ℕ)
    (markers allowed inner outer : Finset (Finset V))
    (S q : Finset V) (x t : V) (c : ℝ) :
    privateRootBadSet r markers allowed (rootFreeEdges x inner) (rootFreeEdges x outer)
      S q x t c = privateRootBadSet r markers allowed inner outer S q x t c := by
  ext A
  simp only [privateRootBadSet, mem_filter, privateRootBad_rootFreeEdges]

/-- Equal observed root-free hosts give exactly equal pre-registered bad sets. -/
theorem privateRootBadSet_congr_observation (r : ℕ)
    (markers allowed inner₁ inner₂ outer₁ outer₂ : Finset (Finset V))
    (S q : Finset V) (x t : V) (c : ℝ)
    (hi : rootFreeEdges x inner₁ = rootFreeEdges x inner₂)
    (ho : rootFreeEdges x outer₁ = rootFreeEdges x outer₂) :
    privateRootBadSet r markers allowed inner₁ outer₁ S q x t c =
      privateRootBadSet r markers allowed inner₂ outer₂ S q x t c := by
  rw [← privateRootBadSet_rootFreeEdges r markers allowed inner₁ outer₁ S q x t c,
    ← privateRootBadSet_rootFreeEdges r markers allowed inner₂ outer₂ S q x t c, hi, ho]

/-- If no structural split is legal, the link is declared bad. This includes
forbidden edges and colliding endpoint/private labels. -/
theorem privateRootBad_of_no_legal_split (r : ℕ)
    (markers allowed inner outer : Finset (Finset V))
    (S q : Finset V) (x t : V) (c : ℝ) (A : Finset V)
    (h : ∀ R uv, ¬ PrivateRootSplitLegal r markers allowed S q x t A R uv) :
    PrivateRootBad r markers allowed inner outer S q x t c A := by
  intro R uv hh
  exact False.elim (h R uv hh)

/-- A link passing the test supplies a legal split and the required actual
completion lower bound. No root-edge presence is assumed. -/
theorem privateRoot_not_bad_witness (r : ℕ)
    (markers allowed inner outer : Finset (Finset V))
    (S q : Finset V) (x t : V) (c : ℝ) (A : Finset V)
    (h : ¬ PrivateRootBad r markers allowed inner outer S q x t c A) :
    ∃ R uv, PrivateRootSplitLegal r markers allowed S q x t A R uv ∧
      c * (completionCount r markers inner (insert x S) q : ℝ) /
          privateRootSourceMean r outer S x ≤
        (privateMigrationSummand r markers inner (insert t S) q x (R,uv) : ℝ) := by
  classical
  unfold PrivateRootBad at h
  push_neg at h
  exact h


/-- When the sampled root edge is present, a structural split becomes a legal
label for the actual injection. Legality itself was registered beforehand. -/
theorem PrivateRootSplitLegal.actual_label {r : ℕ}
    {markers allowed host : Finset (Finset V)} {S q A R uv : Finset V} {x t : V}
    (h : PrivateRootSplitLegal r markers allowed S q x t A R uv)
    (he : insert x A ∈ host) :
    PrivateMigrationLegal r markers host (insert t S) q x R uv := by
  refine { h.split_legal with edge_mem := ?_ }
  rw [mem_singleton.mp h.split_legal.edge_mem]
  exact he

/-- A forbidden root edge is always bad, independently of the observed host. -/
theorem privateRootBad_of_forbidden {r : ℕ}
    {markers allowed inner outer : Finset (Finset V)}
    {S q A : Finset V} {x t : V} {c : ℝ}
    (hforbid : insert x A ∉ allowed) :
    PrivateRootBad r markers allowed inner outer S q x t c A := by
  apply privateRootBad_of_no_legal_split
  intro R uv h
  exact hforbid h.edge_allowed

end LooseHamilton
