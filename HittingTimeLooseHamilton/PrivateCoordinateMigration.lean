module

public import HittingTimeLooseHamilton.PrivateMigrationCounting

public section

/-! # Section 9, equation (privatemap)

The host is fixed throughout. In particular, augmenting the marked pairs does
not reapply the allowed-host filter. Pairs are two-element finite sets, so each
unordered pair occurs just once in the sum.
-/
noncomputable section
namespace LooseHamilton
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {r : ℕ} {markers host : Finset (Finset V)} {D q : Finset V}
  {x : V} {R uv : Finset V}

/-- All marked pairs survive the deletion appearing in a legal summand. -/
theorem privateMigration_markers_survive
    (hD : LegalPrivateCompletion r markers D q)
    (h : PrivateMigrationLegal r markers host D q x R uv) :
    ∀ m ∈ insert uv (insert q markers), m ⊆ univ \ (D ∪ insert x R) := by
  intro m hm v hv
  refine mem_sdiff.mpr ⟨mem_univ _, ?_⟩
  rcases mem_insert.mp hm with rfl | hm
  · intro hvdel
    rcases mem_union.mp hvdel with hd | hp
    · exact disjoint_left.mp h.forbidden_disjoint (mem_union_left _ hv)
        (mem_union_left _ hd)
    · exact disjoint_left.mp h.private_pair_disjoint hp hv
  · have hvD := (mem_sdiff.mp (hD.augmented_subset_active m hm hv)).2
    intro hvdel
    rcases mem_union.mp hvdel with hd | hp
    · exact hvD hd
    · exact disjoint_left.mp h.forbidden_disjoint (mem_union_right _ hp)
        (mem_union_right _ (mem_biUnion.mpr ⟨m, hm, hv⟩))

/-- Each summand is exactly `X` on the surviving vertex subtype. -/
theorem privateMigration_input_card_eq_X (hr : 3 ≤ r)
    (hD : LegalPrivateCompletion r markers D q)
    (h : PrivateMigrationLegal r markers host D q x R uv) :
    (privateMigrationInputFamily r markers host D q x R uv).card =
      unrestrictedCycleCount r
        (restrictEdges (univ \ (D ∪ insert x R)) (insert uv (insert q markers)))
        (inducedHost (univ \ (D ∪ insert x R)) host) := by
  exact cycleOnCount_eq_unrestricted hr _ _ _ (privateMigration_markers_survive hD h)

/-- Migration inequality with a general deleted private block. -/
theorem privateMigration_X_le (hr : 3 ≤ r)
    (hD : LegalPrivateCompletion r markers D q) :
    ∑ a ∈ privateMigrationLabels r markers host D q x,
      unrestrictedCycleCount r
        (restrictEdges (univ \ (D ∪ insert x a.1)) (insert a.2 (insert q markers)))
        (inducedHost (univ \ (D ∪ insert x a.1)) host) ≤
      completionCount r markers host D q := by
  rw [← show (∑ a ∈ privateMigrationLabels r markers host D q x,
      (privateMigrationInputFamily r markers host D q x a.1 a.2).card) = _ from
    sum_congr rfl (fun a ha => privateMigration_input_card_eq_X hr hD
      ((mem_privateMigrationLabels _ _ _ _ _ _ _).mp ha))]
  exact privateMigration_count_le hr

/-- Literal deletion set in equation (privatemap). -/
theorem privateMigration_deleted_eq (S R : Finset V) (x t : V) :
    insert t S ∪ insert x R = S ∪ {x, t} ∪ R := by
  ext v
  simp only [mem_union, mem_insert, mem_singleton]
  tauto

/-- Section 9, equation (privatemap). `q` denotes the unordered pair `yz`.
The legal labels encode precisely the distinctness, old-port avoidance, block
size, and host-edge condition in the manuscript's summation. -/
theorem private_coordinate_migration_general (hr : 3 ≤ r)
    (S : Finset V) (x t : V) (q : Finset V)
    (hframe : LegalPrivateCompletion r markers (insert t S) q) :
    completionCount r markers host (insert t S) q ≥
      ∑ a ∈ privateMigrationLabels r markers host (insert t S) q x,
        unrestrictedCycleCount r
          (restrictEdges (univ \ (S ∪ {x, t} ∪ a.1)) (insert a.2 (insert q markers)))
          (inducedHost (univ \ (S ∪ {x, t} ∪ a.1)) host) := by
  have hs : (∑ a ∈ privateMigrationLabels r markers host (insert t S) q x,
      unrestrictedCycleCount r
        (restrictEdges (univ \ (insert t S ∪ insert x a.1)) (insert a.2 (insert q markers)))
        (inducedHost (univ \ (insert t S ∪ insert x a.1)) host)) =
      ∑ a ∈ privateMigrationLabels r markers host (insert t S) q x,
        unrestrictedCycleCount r
          (restrictEdges (univ \ (S ∪ {x, t} ∪ a.1)) (insert a.2 (insert q markers)))
          (inducedHost (univ \ (S ∪ {x, t} ∪ a.1)) host) := by
    apply sum_congr rfl
    intro a _
    exact congrArg (fun deleted : Finset V => unrestrictedCycleCount r
      (restrictEdges (univ \ deleted) (insert a.2 (insert q markers)))
      (inducedHost (univ \ deleted) host)) (privateMigration_deleted_eq S a.1 x t)
  rw [← hs]
  exact privateMigration_X_le hr hframe

/-- Equation (privatemap) with the paper's named vertices and `|S| = r - 3`.
The pair `{y,z}` and the output private block form a legal completion. -/
theorem private_coordinate_migration (hr : 3 ≤ r)
    (S : Finset V) (x y z t : V) (hS : S.card = r - 3) (ht : t ∉ S)
    (hyz : y ≠ z) (hDq : Disjoint (insert t S) {y, z})
    (hports : Disjoint (insert t S ∪ {y, z}) (originalPorts markers)) :
    completionCount r markers host (insert t S) {y, z} ≥
      ∑ a ∈ privateMigrationLabels r markers host (insert t S) {y, z} x,
        unrestrictedCycleCount r
          (restrictEdges (univ \ (S ∪ {x, t} ∪ a.1))
            (insert a.2 (insert {y, z} markers)))
          (inducedHost (univ \ (S ∪ {x, t} ∪ a.1)) host) := by
  apply private_coordinate_migration_general hr
  refine ⟨?_, ?_, hDq, hports⟩
  · rw [card_insert_of_notMem ht, hS]
    omega
  · simp [hyz]

/-- In uniformity three, the remaining private block is empty, as stated in the
manuscript after (privatemap). -/
theorem privateMigration_rest_empty_three
    (h : PrivateMigrationLegal 3 markers host D q x R uv) : R = ∅ := by
  apply card_eq_zero.mp
  simpa using h.rest_card

end LooseHamilton
