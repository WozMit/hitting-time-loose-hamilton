module

public import HittingTimeLooseHamilton.TerminalFeasibilityFinite

public section

/-! Disjoint complete-edge tests for a prescribed set of low-degree vertices. -/
noncomputable section
open scoped BigOperators
open Finset
namespace LooseHamilton
variable {V : Type*} [Fintype V] [DecidableEq V]

@[expose] def lowSetStar (r : ℕ) (S : Finset V) (v : V) : Finset (Edge V r) :=
  univ.filter (fun e => v ∈ e.val ∧ ∀ w ∈ S, w ∈ e.val → w = v)

@[simp] lemma mem_lowSetStar (r : ℕ) (S : Finset V) (v : V) (e : Edge V r) :
    e ∈ lowSetStar r S v ↔ v ∈ e.val ∧ ∀ w ∈ S, w ∈ e.val → w = v := by
  simp [lowSetStar]

lemma lowSetStar_disjoint (r : ℕ) (S : Finset V) {u v : V}
    (hu : u ∈ S) (huv : u ≠ v) : Disjoint (lowSetStar r S u) (lowSetStar r S v) := by
  apply disjoint_left.mpr
  intro e he hf
  exact huv ((mem_lowSetStar r S v e).mp hf |>.2 u hu ((mem_lowSetStar r S u e).mp he).1)

lemma lowSetStar_card {r : ℕ} (hr : 1 ≤ r) (S : Finset V) {v : V} (hv : v ∈ S) :
    (lowSetStar r S v).card = (Fintype.card V-S.card).choose (r-1) := by
  let A : Finset V := univ \ S
  have hA : A.card = Fintype.card V-S.card := by simp [A,card_sdiff_of_subset (subset_univ S)]
  have hins (e : Finset V) (he : e ∈ A.powersetCard (r-1)) : v ∉ e := by
    intro hve
    exact (mem_sdiff.mp ((mem_powersetCard.mp he).1 hve)).2 hv
  have hcard (e : Finset V) (he : e ∈ A.powersetCard (r-1)) :
      insert v e ∈ completeEdges V r := by
    apply (mem_completeEdges _ _).mpr
    rw [card_insert_of_notMem (hins e he),(mem_powersetCard.mp he).2]
    omega
  calc
    _ = (A.powersetCard (r-1)).card := by
      symm
      apply card_bij (fun e he => (⟨insert v e,hcard e he⟩ : Edge V r))
      · intro e he
        apply (mem_lowSetStar _ _ _ _).mpr
        refine ⟨mem_insert_self _ _,?_⟩
        intro w hw hwe
        rcases mem_insert.mp hwe with h | h
        · exact h
        · exact False.elim ((mem_sdiff.mp ((mem_powersetCard.mp he).1 h)).2 hw)
      · intro e he f hf hef
        have h := congrArg (fun a : Edge V r => a.val.erase v) hef
        simpa only [erase_insert (hins e he),erase_insert (hins f hf)] using h
      · intro e he
        have he' := (mem_lowSetStar _ _ _ _).mp he
        have herase : e.val.erase v ∈ A.powersetCard (r-1) := by
          apply mem_powersetCard.mpr
          constructor
          · intro w hw
            apply mem_sdiff.mpr
            refine ⟨mem_univ _,?_⟩
            intro hwS
            exact (mem_erase.mp hw).1 (he'.2 w hwS (mem_erase.mp hw).2)
          · rw [card_erase_of_mem he'.1,(mem_completeEdges r e.val).mp e.property]
        refine ⟨e.val.erase v,herase,?_⟩
        apply Subtype.ext
        exact insert_erase he'.1
    _ = _ := by rw [card_powersetCard,hA]

@[expose] def lowSetTest (r : ℕ) (S : Finset V) : Finset (Edge V r) :=
  S.biUnion (lowSetStar r S)

lemma lowSetTest_card {r : ℕ} (hr : 1 ≤ r) (S : Finset V) :
    (lowSetTest r S).card = S.card * (Fintype.card V-S.card).choose (r-1) := by
  rw [lowSetTest,card_biUnion (by
    intro u hu v hv huv
    exact lowSetStar_disjoint r S hu huv)]
  calc
    _ = ∑ v ∈ S, (Fintype.card V-S.card).choose (r-1) := sum_congr rfl (fun v hv => lowSetStar_card hr S hv)
    _ = _ := by simp

lemma lowSetTest_inter_card_le (r : ℕ) (S : Finset V) (F : Finset (Edge V r)) :
    (F ∩ lowSetTest r S).card ≤ ∑ v ∈ S, (F ∩ edgeIncidences r v).card := by
  have hs : F ∩ lowSetTest r S ⊆ S.biUnion (fun v => F ∩ edgeIncidences r v) := by
    intro e he
    obtain ⟨v,hv,hev⟩ := mem_biUnion.mp (mem_inter.mp he).2
    apply mem_biUnion.mpr
    exact ⟨v,hv,mem_inter.mpr ⟨(mem_inter.mp he).1,
      mem_edgeIncidences.mpr ((mem_lowSetStar _ _ _ _).mp hev).1⟩⟩
  exact (card_le_card hs).trans card_biUnion_le
end LooseHamilton
