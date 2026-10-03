module

public import HittingTimeLooseHamilton.Models
public import Mathlib.Tactic

public section

/-! Incidence test sets for two low-degree endpoints.

Edges containing both endpoints are discarded. This leaves disjoint stars of
known size; prescribed path edges are then removed before applying a mixed
presence/avoidance estimate.
-/
noncomputable section
namespace LooseHamilton
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

@[expose] def exclusiveStar (r : ℕ) (u v : V) : SimpleHypergraph V :=
  (completeEdges V r).filter fun e => u ∈ e ∧ v ∉ e

@[simp] theorem mem_exclusiveStar (r : ℕ) (u v : V) (e : Finset V) :
    e ∈ exclusiveStar r u v ↔ e.card = r ∧ u ∈ e ∧ v ∉ e := by
  simp [exclusiveStar]

theorem exclusiveStar_disjoint (r : ℕ) (u v : V) :
    Disjoint (exclusiveStar r u v) (exclusiveStar r v u) := by
  apply disjoint_left.mpr
  intro e he hf
  exact ((mem_exclusiveStar r u v e).mp he).2.2
    ((mem_exclusiveStar r v u e).mp hf).2.1

theorem exclusiveStar_card {r : ℕ} (hr : 1 ≤ r) {u v : V} (huv : u ≠ v) :
    (exclusiveStar r u v).card = (Fintype.card V - 2).choose (r-1) := by
  let A : Finset V := univ \ {u,v}
  have hA : A.card = Fintype.card V - 2 := by
    rw [card_sdiff_of_subset (subset_univ _), card_univ]
    simp [huv]
  calc
    (exclusiveStar r u v).card = (A.powersetCard (r-1)).card := by
      symm
      apply card_bij (fun e _ => insert u e)
      · intro e he
        have he' := mem_powersetCard.mp he
        have hu : u ∉ e := by
          intro hu
          exact (mem_sdiff.mp (he'.1 hu)).2 (by simp)
        have hv : v ∉ e := by
          intro hv
          exact (mem_sdiff.mp (he'.1 hv)).2 (by simp)
        apply (mem_exclusiveStar r u v _).mpr
        refine ⟨?_, mem_insert_self _ _, ?_⟩
        · rw [card_insert_of_notMem hu, he'.2]
          omega
        · simp [huv.symm, hv]
      · intro e he f hf hef
        have hu (b : Finset V) (hb : b ∈ A.powersetCard (r-1)) : u ∉ b := by
          intro hu
          exact (mem_sdiff.mp ((mem_powersetCard.mp hb).1 hu)).2 (by simp)
        have h := congrArg (fun b : Finset V => b.erase u) hef
        simpa only [erase_insert (hu e he), erase_insert (hu f hf)] using h
      · intro e he
        have he' := (mem_exclusiveStar r u v e).mp he
        refine ⟨e.erase u, mem_powersetCard.mpr ⟨?_, ?_⟩, insert_erase he'.2.1⟩
        · intro w hw
          apply mem_sdiff.mpr
          refine ⟨mem_univ _, ?_⟩
          simp only [mem_insert, mem_singleton]
          intro h
          rcases h with rfl | rfl
          · exact (mem_erase.mp hw).1 rfl
          · exact he'.2.2 (mem_erase.mp hw).2
        · rw [card_erase_of_mem he'.2.1, he'.1]
    _ = (Fintype.card V - 2).choose (r-1) := by rw [card_powersetCard, hA]

/-- The test edges incident to exactly one endpoint, excluding every fixed
path edge. In particular this set is disjoint from the prescribed edges. -/
@[expose] def endpointDegreeTest (r : ℕ) (u v : V) (K : SimpleHypergraph V) : SimpleHypergraph V :=
  (exclusiveStar r u v ∪ exclusiveStar r v u) \ K

theorem endpointDegreeTest_disjoint (r : ℕ) (u v : V) (K : SimpleHypergraph V) :
    Disjoint (endpointDegreeTest r u v K) K := sdiff_disjoint

theorem endpointDegreeTest_subset (r : ℕ) (u v : V) (K : SimpleHypergraph V) :
    endpointDegreeTest r u v K ⊆ completeEdges V r := by
  intro e he
  rcases mem_union.mp (mem_sdiff.mp he).1 with he | he
  · exact (mem_filter.mp he).1
  · exact (mem_filter.mp he).1

theorem endpointDegreeTest_card_lower {r : ℕ} (hr : 1 ≤ r) {u v : V} (huv : u ≠ v)
    (K : SimpleHypergraph V) :
    2 * (Fintype.card V - 2).choose (r-1) - K.card ≤
      (endpointDegreeTest r u v K).card := by
  have hsum : (exclusiveStar r u v ∪ exclusiveStar r v u).card =
      2 * (Fintype.card V - 2).choose (r-1) := by
    rw [card_union_of_disjoint (exclusiveStar_disjoint r u v),
      exclusiveStar_card hr huv, exclusiveStar_card hr huv.symm]
    omega
  rw [← hsum]
  exact le_card_sdiff _ _

/-- Simultaneously low endpoint degrees force a small intersection with the
whole test set. No probabilistic independence is asserted. -/
theorem endpointDegreeTest_inter_card_le (r : ℕ) (u v : V)
    (K H : SimpleHypergraph V) :
    (H ∩ endpointDegreeTest r u v K).card ≤ vertexDegree H u + vertexDegree H v := by
  have hs : H ∩ endpointDegreeTest r u v K ⊆
      (H.filter fun e => u ∈ e) ∪ (H.filter fun e => v ∈ e) := by
    intro e he
    have heH := (mem_inter.mp he).1
    rcases mem_union.mp (mem_sdiff.mp (mem_inter.mp he).2).1 with he | he
    · exact mem_union_left _ (mem_filter.mpr ⟨heH, ((mem_exclusiveStar r u v e).mp he).2.1⟩)
    · exact mem_union_right _ (mem_filter.mpr ⟨heH, ((mem_exclusiveStar r v u e).mp he).2.1⟩)
  exact (card_le_card hs).trans (card_union_le _ _)
end LooseHamilton
