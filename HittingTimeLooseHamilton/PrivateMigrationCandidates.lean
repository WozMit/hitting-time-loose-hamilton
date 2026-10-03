module

public import HittingTimeLooseHamilton.PrivateMigrationMobility

public section

/-! Directed candidates and their target-coordinate incidences for private moves.
A candidate `(P,u,v)` is incident to each `t ∈ P`, hence at most `r-2` targets.
Bad unordered labels are images of bad directed candidates. Removing this image
removes both bad orientations; no directed-to-unordered good-count equality is
asserted. The root-link fraction is measured directly in unordered labels.
-/
noncomputable section
namespace LooseHamilton
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Bad directed candidates in which `t` is one of the private vertices. -/
@[expose] def privateBadCandidateFiber (bad : Finset (Finset V × V × V)) (t : V) :=
  bad.filter fun c => t ∈ c.1

/-- Forget the target private vertex and the orientation of the marked pair. -/
@[expose] def privateCandidateLabel (t : V) (c : Finset V × V × V) : Finset V × Finset V :=
  (c.1.erase t, {c.2.1, c.2.2})

/-- A label is bad when either directed orientation is bad. -/
@[expose] def privateBadLabels (bad : Finset (Finset V × V × V)) (t : V) :=
  (privateBadCandidateFiber bad t).image (privateCandidateLabel t)

theorem privateBadLabels_card_le (bad : Finset (Finset V × V × V)) (t : V) :
    (privateBadLabels bad t).card ≤ (privateBadCandidateFiber bad t).card :=
  card_image_le

/-- The auxiliary-frame candidate count on the source space deleting `S ∪ {x}`.
The candidate private block is further deleted, and its pair is inserted as a
marker. Thus this is the same actual `X` used in the injection. -/
@[expose] def privateCandidateCompletionCount (r : ℕ) (markers host : Finset (Finset V))
    (S q : Finset V) (x : V) (c : Finset V × V × V) : ℕ :=
  unrestrictedCycleCount r
    (restrictEdges (univ \ (insert x S ∪ c.1))
      (insert {c.2.1,c.2.2} (insert q markers)))
    (inducedHost (univ \ (insert x S ∪ c.1)) host)

theorem privateCandidateCompletionCount_eq_summand (r : ℕ)
    (markers host : Finset (Finset V)) (S q R : Finset V) (x t u v : V) :
    privateCandidateCompletionCount r markers host S q x (insert t R,u,v) =
      privateMigrationSummand r markers host (insert t S) q x (R,{u,v}) := by
  have he : insert x S ∪ insert t R = insert t S ∪ insert x R := by
    ext z
    simp only [mem_union, mem_insert]
    tauto
  dsimp only [privateCandidateCompletionCount, privateMigrationSummand]
  rw [he]

/-- A good unordered label has no bad orientation in the source candidate set. -/
theorem privateCandidate_not_bad {r : ℕ} {markers host : Finset (Finset V)}
    {S q R : Finset V} {x t u v : V}
    (hlegal : PrivateMigrationLegal r markers host (insert t S) q x R {u,v})
    (bad : Finset (Finset V × V × V))
    (hgood : (R,{u,v}) ∉ privateBadLabels bad t) :
    (insert t R,u,v) ∉ bad := by
  have ht : t ∉ R := by
    intro ht
    exact disjoint_left.mp hlegal.forbidden_disjoint
      (mem_union_right _ (mem_insert_of_mem ht)) (mem_union_left _ (mem_insert_self _ _))
  intro hc
  apply hgood
  apply mem_image.mpr
  refine ⟨(insert t R,u,v), mem_filter.mpr ⟨hc, mem_insert_self _ _⟩, ?_⟩
  simp [privateCandidateLabel, ht]

/-- Candidate balance and a sampled root link imply one private move. Candidate
balance is imposed on actual legal source candidates, not on the target count.
The host, and therefore its allowed-edge filter, stays fixed throughout. -/
theorem private_coordinate_mobility_of_candidate_balance
    {r : ℕ} {markers host : Finset (Finset V)}
    (S q : Finset V) (x t : V) (hr : 3 ≤ r)
    (hD : LegalPrivateCompletion r markers (insert t S) q)
    (bad : Finset (Finset V × V × V))
    (κ lam μ : ℝ) (hlam : 0 ≤ lam) (hμ : 0 < μ)
    (hlink : κ * migrationRootDegree host x ≤
      ((privateMigrationLabels r markers host (insert t S) q x \
        privateBadLabels bad t).card : ℝ))
    (hbalance : ∀ R u v,
      PrivateMigrationLegal r markers host (insert t S) q x R {u,v} →
      (insert t R,u,v) ∉ bad →
      lam * (completionCount r markers host (insert x S) q : ℝ) / μ ≤
        privateCandidateCompletionCount r markers host S q x (insert t R,u,v)) :
    κ * lam * (migrationRootDegree host x : ℝ) / μ *
        (completionCount r markers host (insert x S) q : ℝ) ≤
      completionCount r markers host (insert t S) q := by
  apply private_coordinate_mobility S q x t hr hD
    (privateMigrationLabels r markers host (insert t S) q x \ privateBadLabels bad t)
    sdiff_subset κ lam μ hlam hμ hlink
  intro a ha
  obtain ⟨ha, hnot⟩ := mem_sdiff.mp ha
  have hlegal := (mem_privateMigrationLabels _ _ _ _ _ _ _).mp ha
  obtain ⟨u,v,huv,hpair⟩ := card_eq_two.mp hlegal.pair_card
  have hp : a = (a.1,{u,v}) := Prod.ext rfl hpair
  rw [hp] at hlegal hnot ⊢
  have hb := hbalance a.1 u v hlegal (privateCandidate_not_bad hlegal bad hnot)
  rwa [privateCandidateCompletionCount_eq_summand] at hb

end LooseHamilton
