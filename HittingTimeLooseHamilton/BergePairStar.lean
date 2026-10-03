module

public import HittingTimeLooseHamilton.EndpointLowDegreeTestSet

public section

/-! Counting complete hyperedges through a prescribed pair of distinct vertices. -/
noncomputable section
namespace LooseHamilton
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

@[expose] def pairStar (r : ℕ) (u v : V) : SimpleHypergraph V :=
  (completeEdges V r).filter fun e => u ∈ e ∧ v ∈ e

@[simp] theorem mem_pairStar (r : ℕ) (u v : V) (e : Finset V) :
    e ∈ pairStar r u v ↔ e.card = r ∧ u ∈ e ∧ v ∈ e := by
  simp [pairStar]

theorem pairStar_card {r : ℕ} (hr : 2 ≤ r) {u v : V} (huv : u ≠ v) :
    (pairStar r u v).card = (Fintype.card V - 2).choose (r-2) := by
  let A : Finset V := univ \ {u,v}
  have hA : A.card = Fintype.card V - 2 := by
    rw [card_sdiff_of_subset (subset_univ _), card_univ]
    simp [huv]
  have hnot (e : Finset V) (he : e ∈ A.powersetCard (r-2)) : u ∉ e ∧ v ∉ e := by
    constructor <;> intro hv
    · exact (mem_sdiff.mp ((mem_powersetCard.mp he).1 hv)).2 (by simp)
    · exact (mem_sdiff.mp ((mem_powersetCard.mp he).1 hv)).2 (by simp)
  calc
    (pairStar r u v).card = (A.powersetCard (r-2)).card := by
      symm
      apply card_bij (fun e _ => insert u (insert v e))
      · intro e he
        obtain ⟨hu,hv⟩ := hnot e he
        apply (mem_pairStar r u v _).mpr
        refine ⟨?_, by simp, by simp⟩
        rw [card_insert_of_notMem (by simp [huv, hu]), card_insert_of_notMem hv,
          (mem_powersetCard.mp he).2]
        omega
      · intro e he f hf hef
        have h := congrArg (fun b : Finset V => (b.erase u).erase v) hef
        simpa [huv, (hnot e he).1, (hnot e he).2, (hnot f hf).1, (hnot f hf).2] using h
      · intro e he
        obtain ⟨hc,hu,hv⟩ := (mem_pairStar r u v e).mp he
        refine ⟨e \ {u,v}, mem_powersetCard.mpr ⟨?_, ?_⟩, ?_⟩
        · exact sdiff_subset_sdiff (subset_univ _) (Subset.refl _)
        · rw [card_sdiff_of_subset (show {u,v} ⊆ e from insert_subset_iff.mpr ⟨hu, singleton_subset_iff.mpr hv⟩), hc]
          simp [huv]
        · ext w
          simp only [mem_insert, mem_sdiff, mem_singleton]
          constructor
          · rintro (rfl | rfl | ⟨hw,_⟩) <;> assumption
          · intro hw
            by_cases hwu : w=u
            · exact Or.inl hwu
            · by_cases hwv : w=v
              · exact Or.inr (Or.inl hwv)
              · exact Or.inr (Or.inr ⟨hw, not_or.mpr ⟨hwu,hwv⟩⟩)
    _ = (Fintype.card V - 2).choose (r-2) := by rw [card_powersetCard, hA]
end LooseHamilton
