module

public import HittingTimeLooseHamilton.KahnRevealData
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

public section

/-! Cardinality of the available set in terms of untouched matching blocks. -/
noncomputable section
open scoped BigOperators
namespace Kahn.PerfectMatching
variable {n r : ℕ} (M : Kahn.PerfectMatching n r)

/-- Blocks none of whose vertices has yet appeared before `v`. -/
@[expose] def lateBlocks (σ : Equiv.Perm (Fin n)) (v : Fin n) : Finset (Finset (Fin n)) :=
  M.val.filter fun B => ∀ w ∈ B, σ v ≤ σ w

lemma lateBlocks_disjoint (σ : Equiv.Perm (Fin n)) (v : Fin n) :
    (M.lateBlocks σ v : Set (Finset (Fin n))).PairwiseDisjoint id := by
  intro A hA B hB hne
  apply Finset.disjoint_left.mpr
  intro x hxA hxB
  apply hne
  exact (M.eq_edge_of_mem (Finset.mem_filter.mp hA).1 hxA).trans
    (M.eq_edge_of_mem (Finset.mem_filter.mp hB).1 hxB).symm

lemma unexposed_eq_biUnion_lateBlocks (σ : Equiv.Perm (Fin n)) (v : Fin n) :
    Finset.univ \ M.earlierEdges σ v = (M.lateBlocks σ v).biUnion id := by
  ext x
  simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_biUnion]
  constructor
  · intro h
    refine ⟨M.edge x, Finset.mem_filter.mpr ⟨M.edge_mem x, ?_⟩, M.mem_edge x⟩
    exact (M.not_mem_earlierEdges σ v x).mp h
  · rintro ⟨B, hB, hxB⟩
    obtain ⟨hBM, hlate⟩ := Finset.mem_filter.mp hB
    apply (M.not_mem_earlierEdges σ v x).mpr
    have he : B = M.edge x := M.eq_edge_of_mem hBM hxB
    rwa [← he]

lemma unexposed_card (σ : Equiv.Perm (Fin n)) (v : Fin n) :
    (Finset.univ \ M.earlierEdges σ v).card = (M.lateBlocks σ v).card * r := by
  rw [M.unexposed_eq_biUnion_lateBlocks, Finset.card_biUnion (M.lateBlocks_disjoint σ v)]
  calc
    ∑ B ∈ M.lateBlocks σ v, (id B).card = ∑ _B ∈ M.lateBlocks σ v, r := by
      apply Finset.sum_congr rfl
      intro B hB
      exact M.property.1 B (Finset.mem_filter.mp hB).1
    _ = (M.lateBlocks σ v).card * r := by simp

/-- On the unknown branch, the available set has one fewer vertex than a union
of whole matching blocks, as used in (35). -/
lemma available_card (σ : Equiv.Perm (Fin n)) (v : Fin n)
    (hfirst : v ∉ M.earlierEdges σ v) :
    (M.available σ v).card = (M.lateBlocks σ v).card * r - 1 := by
  rw [available, Finset.card_erase_of_mem (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hfirst⟩)]
  rw [M.unexposed_card]

lemma own_edge_mem_lateBlocks_iff (σ : Equiv.Perm (Fin n)) (v : Fin n) :
    M.edge v ∈ M.lateBlocks σ v ↔ v ∉ M.earlierEdges σ v := by
  simp only [lateBlocks, Finset.mem_filter, M.edge_mem v, true_and]
  exact (M.unknown_iff_first σ v).symm

lemma lateBlocks_card_pos (σ : Equiv.Perm (Fin n)) (v : Fin n)
    (hfirst : v ∉ M.earlierEdges σ v) : 0 < (M.lateBlocks σ v).card := by
  apply Finset.card_pos.mpr
  exact ⟨M.edge v, (M.own_edge_mem_lateBlocks_iff σ v).mpr hfirst⟩

lemma lateBlocks_card_le (σ : Equiv.Perm (Fin n)) (v : Fin n) :
    (M.lateBlocks σ v).card ≤ M.val.card :=
  Finset.card_le_card (Finset.filter_subset _ _)

end Kahn.PerfectMatching
