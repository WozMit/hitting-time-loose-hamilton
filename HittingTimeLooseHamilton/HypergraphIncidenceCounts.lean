module

public import HittingTimeLooseHamilton.Models
public import HittingTimeLooseHamilton.KahnOrdering

public section

/-! Exact incidence counts for complete uniform hypergraphs and their process states. -/
noncomputable section
namespace LooseHamilton
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Complete r-edges incident with a specified vertex. -/
@[expose] def edgeIncidences (r : ℕ) (v : V) : Finset (Edge V r) :=
  univ.filter (fun e => v ∈ e.val)

/-- Complete r-edges incident with both specified vertices. -/
@[expose] def pairIncidences (r : ℕ) (u v : V) : Finset (Edge V r) :=
  univ.filter (fun e => u ∈ e.val ∧ v ∈ e.val)

@[simp] theorem mem_edgeIncidences {r : ℕ} {v : V} {e : Edge V r} :
    e ∈ edgeIncidences r v ↔ v ∈ e.val := by simp [edgeIncidences]

@[simp] theorem mem_pairIncidences {r : ℕ} {u v : V} {e : Edge V r} :
    e ∈ pairIncidences r u v ↔ u ∈ e.val ∧ v ∈ e.val := by simp [pairIncidences]

theorem edgeIncidences_inter (r : ℕ) (u v : V) :
    edgeIncidences r u ∩ edgeIncidences r v = pairIncidences r u v := by ext; simp

/-- The fixed-subset incidence formula before specialising to one or two vertices. -/
theorem completeEdges_containing_card (r : ℕ) (A : Finset V) (hAr : A.card ≤ r) :
    ((univ : Finset (Edge V r)).filter (fun e => A ⊆ e.val)).card =
      (Fintype.card V - A.card).choose (r - A.card) := by
  have hc := Kahn.Ordering.card_subsets_containing (univ : Finset V) A (subset_univ _) r hAr
  rw [card_univ] at hc
  rw [← hc]
  apply card_bij (fun e _ => e.val)
  · intro e he
    simp only [mem_filter, mem_univ, true_and] at he
    exact mem_filter.mpr ⟨mem_powersetCard.mpr ⟨subset_univ _,
      (mem_completeEdges r e.val).mp e.property⟩, he⟩
  · intro e _ f _ h
    exact Subtype.ext h
  · intro e he
    obtain ⟨he, hAe⟩ := mem_filter.mp he
    refine ⟨⟨e, (mem_completeEdges r e).mpr (mem_powersetCard.mp he).2⟩, ?_, rfl⟩
    simp [hAe]

theorem edgeIncidences_card {r : ℕ} (hr : 1 ≤ r) (v : V) :
    (edgeIncidences r v).card = (Fintype.card V - 1).choose (r - 1) := by
  simpa [edgeIncidences] using completeEdges_containing_card r {v} (by simpa using hr)

theorem pairIncidences_card {r : ℕ} (hr : 2 ≤ r) {u v : V} (huv : u ≠ v) :
    (pairIncidences r u v).card = (Fintype.card V - 2).choose (r - 2) := by
  have hc : ({u,v} : Finset V).card = 2 := by simp [huv]
  simpa [pairIncidences, hc, insert_subset_iff, singleton_subset_iff] using completeEdges_containing_card r {u,v} (by omega)

/-- Inclusion-exclusion without truncated subtraction. -/
theorem edgeIncidences_union_card_add {r : ℕ} (hr : 2 ≤ r) {u v : V} (huv : u ≠ v) :
    (edgeIncidences r u ∪ edgeIncidences r v).card +
      (Fintype.card V - 2).choose (r - 2) =
        2 * (Fintype.card V - 1).choose (r - 1) := by
  rw [← pairIncidences_card hr huv, ← edgeIncidences_inter, card_union_add_card_inter,
    edgeIncidences_card (by omega), edgeIncidences_card (by omega)]
  omega

theorem edgeIncidences_union_card {r : ℕ} (hr : 2 ≤ r) {u v : V} (huv : u ≠ v) :
    (edgeIncidences r u ∪ edgeIncidences r v).card =
      2 * (Fintype.card V - 1).choose (r - 1) -
        (Fintype.card V - 2).choose (r - 2) := by
  have := edgeIncidences_union_card_add hr huv
  omega

/-- A process vertex has degree zero precisely when all incident edges occur later. -/
theorem processState_degree_zero_iff {r : ℕ} (σ : EdgeOrder V r) (t : ℕ) (v : V) :
    vertexDegree (processState σ t) v = 0 ↔
      ∀ e ∈ edgeIncidences r v, t ≤ edgeRank σ e := by
  simp only [vertexDegree, card_eq_zero, filter_eq_empty_iff]
  constructor
  · intro h e he
    by_contra hn
    have heG : e.val ∈ processState σ t :=
      mem_image.mpr ⟨e, by simp [Nat.lt_of_not_ge hn], rfl⟩
    exact h heG ((mem_edgeIncidences).mp he)
  · intro h e he hv
    obtain ⟨a, ha, rfl⟩ := mem_image.mp he
    have ht : edgeRank σ a < t := by simpa using ha
    exact (Nat.not_lt_of_ge (h a (by simpa using hv))) ht

/-- Joint isolation is avoidance of the union of the two incidence supports. -/
theorem processState_two_degrees_zero_iff {r : ℕ} (σ : EdgeOrder V r) (t : ℕ) (u v : V) :
    (vertexDegree (processState σ t) u = 0 ∧ vertexDegree (processState σ t) v = 0) ↔
      ∀ e ∈ edgeIncidences r u ∪ edgeIncidences r v, t ≤ edgeRank σ e := by
  rw [processState_degree_zero_iff, processState_degree_zero_iff]
  simp only [mem_union, or_imp, forall_and]

end LooseHamilton
