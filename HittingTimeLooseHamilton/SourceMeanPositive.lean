module

public import HittingTimeLooseHamilton.CompletionParameters
public import HittingTimeLooseHamilton.Setup

public section

/-! Actual source cycles force positive outer induced mean. No positivity
hypothesis on the normalization, and no large-order hypothesis, is needed. -/
noncomputable section
namespace LooseHamilton
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A nonempty cycle family gives both surviving vertices and actual outer edges. -/
theorem inducedHost_positive_of_cycleOnCount {r : ℕ} {S : Finset V}
    {M G H : Finset (Finset V)} (hGH : G ⊆ H)
    (hX : 0 < cycleOnCount r S M G) :
    0 < S.card ∧ 0 < (inducedHost S H).card := by
  obtain ⟨E,hE⟩ := card_pos.mp hX
  obtain ⟨⟨C⟩,hEG⟩ := (mem_cycleOnFamily _ _ _ _ _).mp hE
  have hlen : 0 < C.length := by have := C.length_ge; omega
  refine ⟨card_pos.mpr ⟨C.junction ⟨0,hlen⟩, C.junction_mem _⟩, ?_⟩
  have he : 0 < (restrictEdges S E).card := C.restrict.edges_card_pos
  exact lt_of_lt_of_le he (card_le_card
    (restrictEdges_subset_inducedHost S E H (fun _ h => C.edge_subset_active h)
      (fun _ h => hGH (hEG h))))

/-- The normalization of a real, positive source count is strictly positive. -/
theorem inducedMean_pos_of_cycleOnCount {r : ℕ} {S : Finset V}
    {M G H : Finset (Finset V)} (hr : 0 < r) (hGH : G ⊆ H)
    (hX : 0 < cycleOnCount r S M G) :
    0 < meanDegree (V := ↥S) r (inducedHost S H).card := by
  obtain ⟨hS,hH⟩ := inducedHost_positive_of_cycleOnCount hGH hX
  unfold meanDegree
  rw [Fintype.card_coe]
  exact div_pos (mul_pos (Nat.cast_pos.mpr hr) (Nat.cast_pos.mpr hH))
    (Nat.cast_pos.mpr hS)

/-- Specialization to an actual private-block completion, including augmented markers. -/
theorem inducedMean_pos_of_completionCount {r : ℕ} {P q : Finset V}
    {M G H : Finset (Finset V)} (hr : 0 < r) (hGH : G ⊆ H)
    (hX : 0 < completionCount r M G P q) :
    0 < meanDegree (V := ↥(univ \ P)) r (inducedHost (univ \ P) H).card :=
  inducedMean_pos_of_cycleOnCount hr hGH hX

end LooseHamilton
