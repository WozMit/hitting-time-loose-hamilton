module

public import HittingTimeLooseHamilton.CycleSurgery
public import HittingTimeLooseHamilton.Setup

public section

/-! Simultaneous expansion of disjoint marked pairs.
Each step invokes the existing one-marker cycle surgery, so connectedness is
preserved constructively throughout the expansion. -/
noncomputable section
namespace LooseHamilton
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Expand every marker using its assigned private block. The result has exactly
the old ordinary edges together with the expanded markers, and covers exactly
the old active vertices together with all assigned private vertices. -/
theorem expand_all_markers {r : ℕ} (hr : 3 ≤ r)
    (M : Finset (Finset V)) (P : Finset V → Finset V)
    {W : Finset V} {E : Finset (Finset V)}
    (hC : IsMixedCycleOn r W M E)
    (hcard : ∀ p ∈ M, (P p).card = r - 2)
    (houtside : ∀ p ∈ M, Disjoint (P p) W)
    (hblocks : (M : Set (Finset V)).PairwiseDisjoint P) :
    IsMixedCycleOn r (W ∪ M.biUnion P) ∅
      (E ∪ M.image (fun p => p ∪ P p)) := by
  induction M using Finset.induction_on generalizing W E with
  | empty => simpa using hC
  | @insert p M hp ih =>
    obtain ⟨C⟩ := hC
    have hpM : p ∈ insert p M := mem_insert_self _ _
    have hP : (P p).Nonempty := card_pos.mp (by rw [hcard p hpM]; omega)
    have hfresh : p ∪ P p ∉ E := by
      intro hE
      obtain ⟨x,hx⟩ := hP
      exact disjoint_left.mp (houtside p hpM) hx
        (C.edge_subset_active hE (mem_union_right _ hx))
    have hnext : IsMixedCycleOn r (W ∪ P p) M (insert (p ∪ P p) E) := by
      refine ⟨?_⟩
      simpa only [erase_insert hp] using
        C.expand ⟨p,hpM⟩ (P p) (hcard p hpM) (houtside p hpM) hfresh
    have hcard' : ∀ q ∈ M, (P q).card = r - 2 :=
      fun q hq => hcard q (mem_insert_of_mem hq)
    have houtside' : ∀ q ∈ M, Disjoint (P q) (W ∪ P p) := by
      intro q hq
      apply disjoint_union_right.mpr
      refine ⟨houtside q (mem_insert_of_mem hq), ?_⟩
      apply hblocks (mem_insert_of_mem hq) hpM
      intro heq
      exact hp (heq ▸ hq)
    have hblocks' : (M : Set (Finset V)).PairwiseDisjoint P :=
      fun q hq s hs hqs => hblocks (mem_insert_of_mem hq) (mem_insert_of_mem hs) hqs
    have hresult := ih hnext hcard' houtside' hblocks'
    have hW : (W ∪ P p) ∪ M.biUnion P = W ∪ (insert p M).biUnion P := by
      rw [biUnion_insert]
      exact union_assoc _ _ _
    have hE : insert (p ∪ P p) E ∪ M.image (fun q => q ∪ P q) =
        E ∪ (insert p M).image (fun q => q ∪ P q) := by
      ext e
      simp only [mem_union,mem_insert,mem_image]
      constructor
      · rintro ((rfl | he) | ⟨q,hq,rfl⟩)
        · exact Or.inr ⟨p,Or.inl rfl,rfl⟩
        · exact Or.inl he
        · exact Or.inr ⟨q,Or.inr hq,rfl⟩
      · rintro (he | ⟨q,hq,rfl⟩)
        · exact Or.inl (Or.inr he)
        · rcases hq with rfl | hq
          · exact Or.inl (Or.inl rfl)
          · exact Or.inr ⟨q,hq,rfl⟩
    rw [hW,hE] at hresult
    exact hresult

/-- A spanning connected mixed cycle lifts to an ordinary loose Hamilton cycle
when each marker is expanded to a host edge and the private blocks fill the
omitted vertices. -/
theorem looseHamiltonCycle_of_expanded_markers {r : ℕ} (hr : 3 ≤ r)
    (M : Finset (Finset V)) (P : Finset V → Finset V)
    {W : Finset V} {E F : Finset (Finset V)}
    (hC : IsMixedCycleOn r W M E)
    (hcard : ∀ p ∈ M, (P p).card = r - 2)
    (houtside : ∀ p ∈ M, Disjoint (P p) W)
    (hblocks : (M : Set (Finset V)).PairwiseDisjoint P)
    (hcover : W ∪ M.biUnion P = univ)
    (hE : E ⊆ F) (hexpanded : ∀ p ∈ M, p ∪ P p ∈ F) :
    HasLooseHamiltonCycle r F := by
  have hcycle := expand_all_markers hr M P hC hcard houtside hblocks
  rw [hcover] at hcycle
  refine ⟨E ∪ M.image (fun p => p ∪ P p), union_subset hE ?_,
    isMixedCycleOn_univ_iff.mp hcycle⟩
  intro e he
  obtain ⟨p,hp,rfl⟩ := mem_image.mp he
  exact hexpanded p hp
end LooseHamilton
