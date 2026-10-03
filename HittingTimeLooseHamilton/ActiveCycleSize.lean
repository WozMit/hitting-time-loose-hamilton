module

public import HittingTimeLooseHamilton.CycleOn

public section

/-! # Quantitative size safeguards for endpoint cuts -/
namespace LooseHamilton
namespace MixedCycleOnWitness
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {r : ℕ} {S : Finset V} {markers edges : Finset (Finset V)}

theorem active_length_eq (C : MixedCycleOnWitness r S markers edges) :
    C.length = markers.card + edges.card := by
  simpa using Fintype.card_congr C.slot

theorem active_junction_card (C : MixedCycleOnWitness r S markers edges) :
    (univ.image C.junction).card = C.length := by
  rw [card_image_of_injective _ C.junction_injective]
  simp

theorem active_private_union_card (C : MixedCycleOnWitness r S markers edges) :
    (univ.biUnion C.privateBlock).card = (r - 2) * edges.card := by
  rw [card_biUnion]
  · simp [C.private_card, Nat.mul_comm]
  · intro e _ f _ hef
    exact C.private_disjoint hef

theorem active_card_eq (C : MixedCycleOnWitness r S markers edges) (hr : 3 ≤ r) :
    S.card = (r - 1) * edges.card + markers.card := by
  have hd : Disjoint (univ.image C.junction) (univ.biUnion C.privateBlock) := by
    rw [disjoint_biUnion_right]
    intro e _
    exact C.junction_private_disjoint e
  rw [C.cover, card_union_of_disjoint hd, C.active_junction_card,
    C.active_private_union_card, C.active_length_eq]
  have hstep : r - 1 = (r - 2) + 1 := by omega
  rw [hstep, Nat.add_mul]
  omega

/-- A cycle with at most five slots has at most `5*(r-1)` active vertices. -/
theorem active_card_le_length (C : MixedCycleOnWitness r S markers edges) (hr : 3 ≤ r) :
    S.card ≤ (r - 1) * C.length := by
  rw [C.active_card_eq hr, C.active_length_eq, Nat.mul_add]
  have hm : markers.card ≤ (r - 1) * markers.card := by
    simpa using Nat.mul_le_mul_right markers.card (show 1 ≤ r - 1 by omega)
  omega

/-- The manuscript's large-size setting excludes every short contracted core.
Type I removes one slot and Type II removes three. -/
theorem six_le_length_of_active_card (C : MixedCycleOnWitness r S markers edges)
    (hr : 3 ≤ r) (hsize : 5 * (r - 1) < S.card) : 6 ≤ C.length := by
  have h := C.active_card_le_length hr
  by_contra hn
  have hlen : C.length ≤ 5 := by omega
  have hmul := Nat.mul_le_mul_left (r - 1) hlen
  omega

end MixedCycleOnWitness
end LooseHamilton
