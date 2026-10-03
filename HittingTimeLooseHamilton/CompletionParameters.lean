module

public import HittingTimeLooseHamilton.CompletionModels

public section

/-! # Parameters after private-block contraction

Deleting an `(r-2)`-set and adding its fresh endpoint pair changes the
parameters from `(N,s,k)` to `(N-(r-2),s+1,k-1)`.
-/
namespace LooseHamilton
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem restrictEdges_card (S : Finset V) (E : Finset (Finset V))
    (hE : ∀ e ∈ E, e ⊆ S) : (restrictEdges S E).card = E.card := by
  simpa using (Fintype.card_congr (restrictedEdgeEquiv S E hE)).symm

namespace MixedCycleOnWitness
variable {r : ℕ} {S : Finset V} {markers edges : Finset (Finset V)}

theorem vertex_card (C : MixedCycleOnWitness r S markers edges) (hr : 3 ≤ r) :
    S.card = (r-1) * edges.card + markers.card := by
  have h := C.restrict.vertex_card hr
  simpa only [Fintype.card_coe,
    restrictEdges_card S markers (fun _ h => C.marked_subset_active h),
    restrictEdges_card S edges (fun _ h => C.edge_subset_active h)] using h
end MixedCycleOnWitness

namespace LegalPrivateCompletion
variable {r : ℕ} {markers : Finset (Finset V)} {P pair : Finset V}

theorem pair_not_mem (h : LegalPrivateCompletion r markers P pair) : pair ∉ markers := by
  intro hp
  have hn : pair.Nonempty := card_pos.mp (by rw [h.pair_card]; omega)
  obtain ⟨x,hx⟩ := hn
  exact disjoint_left.mp h.ports_disjoint (mem_union_right _ hx)
    (mem_biUnion.mpr ⟨pair,hp,hx⟩)

theorem augmented_card (h : LegalPrivateCompletion r markers P pair) :
    (insert pair markers).card = markers.card + 1 := by simp [h.pair_not_mem]

theorem active_card (h : LegalPrivateCompletion r markers P pair) :
    (univ \ P).card = Fintype.card V - (r-2) := by
  rw [card_sdiff_of_subset (subset_univ P), card_univ, h.private_card]

theorem active_fintype_card (h : LegalPrivateCompletion r markers P pair) :
    Fintype.card ↥(univ \ P) = Fintype.card V - (r-2) := by
  rw [Fintype.card_coe]
  exact h.active_card

theorem restricted_augmented_card (h : LegalPrivateCompletion r markers P pair) :
    (restrictEdges (univ \ P) (insert pair markers)).card = markers.card + 1 := by
  rw [restrictEdges_card _ _ h.augmented_subset_active, h.augmented_card]

/-- Every completion has exactly one fewer ordinary edge. -/
theorem completion_edge_card (h : LegalPrivateCompletion r markers P pair)
    (hr : 3 ≤ r) {k : ℕ}
    (hN : Fintype.card V = (r-1)*k + markers.card)
    {F : Finset (Finset V)} (hF : IsMixedCycleOn r (univ \ P) (insert pair markers) F) :
    F.card = k-1 := by
  obtain ⟨C⟩ := hF
  have hc := C.vertex_card hr
  rw [h.active_card, h.augmented_card] at hc
  have hP : r-2 ≤ Fintype.card V := by
    rw [← h.private_card]
    exact card_le_univ P
  have hactive : Fintype.card V = (r-1)*F.card + (markers.card+1) + (r-2) := by
    omega
  have hstep : r-1 = (r-2)+1 := by omega
  have hmul : (r-1)*k = (r-1)*(F.card+1) := by
    rw [mul_add, mul_one]
    omega
  have heq : k = F.card+1 := Nat.eq_of_mul_eq_mul_left (by omega : 0 < r-1) hmul
  omega

/-- All three parameter changes, in the actual surviving vertex subtype. -/
theorem parameters (h : LegalPrivateCompletion r markers P pair)
    (hr : 3 ≤ r) {k : ℕ}
    (hN : Fintype.card V = (r-1)*k + markers.card)
    {F : Finset (Finset V)} (hF : IsMixedCycleOn r (univ \ P) (insert pair markers) F) :
    Fintype.card ↥(univ \ P) = Fintype.card V - (r-2) ∧
    (restrictEdges (univ \ P) (insert pair markers)).card = markers.card+1 ∧
    F.card = k-1 :=
  ⟨h.active_fintype_card, h.restricted_augmented_card, h.completion_edge_card hr hN hF⟩
end LegalPrivateCompletion
end LooseHamilton
