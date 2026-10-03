module

public import HittingTimeLooseHamilton.CompletionMatching
public import HittingTimeLooseHamilton.BoundaryEnumeration
public import HittingTimeLooseHamilton.Enumeration
public import HittingTimeLooseHamilton.NormalizationFactorials

public section

/-! # Complete-host counts after private contraction

The existing enumeration theorem is reused for at least three remaining
ordinary edges. The two-edge extension handles the sharp boundary of the
normalization proposition without strengthening its hypotheses.
-/
noncomputable section
open Finset
namespace LooseHamilton
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The numerator completion count has exactly the contracted factorial formula. -/
theorem completionCount_complete_formula {r k : ℕ} {markers : Finset (Finset V)}
    {P pair : Finset V} (hr : 3 ≤ r) (hM : IsPairMatching markers)
    (root : ↥markers) (h : LegalPrivateCompletion r markers P pair)
    (hks : markers.card + 2 ≤ k)
    (hN : Fintype.card V = (r - 1) * k + markers.card) :
    completionCount r markers (completeEdges V r) P pair =
      completeHostFormula r (Fintype.card V - (r - 2)) (k - 1) (markers.card + 1) := by
  rw [completionCount_eq_X hr h, inducedHost_completeEdges]
  have hs : 1 ≤ markers.card := card_pos.mpr ⟨root.val, root.property⟩
  have hk : 3 ≤ k := by omega
  have hn : Fintype.card ↥(univ \ P) =
      (r-1)*(k-1) + (restrictEdges (univ \ P) (insert pair markers)).card := by
    rw [h.active_fintype_card, h.restricted_augmented_card]
    have he : (r-1)*(k-1)+(r-1) = (r-1)*k := by
      rw [← Nat.mul_succ]; congr 1; omega
    have hP : r-2 ≤ Fintype.card V := by rw [← h.private_card]; exact card_le_univ P
    omega
  have hsk : (restrictEdges (univ \ P) (insert pair markers)).card ≤ k-1 := by
    rw [h.restricted_augmented_card]
    omega
  have hc : unrestrictedCycleCount r (restrictEdges (univ \ P) (insert pair markers))
      (completeEdges ↥(univ \ P) r) =
      completeHostFormula r (Fintype.card ↥(univ \ P)) (k-1)
        (restrictEdges (univ \ P) (insert pair markers)).card := by
    by_cases hk4 : 4 ≤ k
    · exact completeHost_count hr (h.restricted_matching hM)
        (completionRestrictedRoot markers P pair root).property (by omega) hsk hn
    · exact completeHost_count_ge_two hr (h.restricted_matching hM)
        (completionRestrictedRoot markers P pair root).property (by omega) hsk hn
  simpa only [h.active_fintype_card, h.restricted_augmented_card] using hc

/-- The denominator in the directed ratio is positive throughout the stated range. -/
theorem completeHost_cycleCount_pos {r k : ℕ} {markers : Finset (Finset V)}
    (hr : 3 ≤ r) (hM : IsPairMatching markers) (root : ↥markers)
    (hks : markers.card + 2 ≤ k)
    (hN : Fintype.card V = (r - 1) * k + markers.card) :
    0 < unrestrictedCycleCount r markers (completeEdges V r) := by
  have hs : 1 ≤ markers.card := card_pos.mpr ⟨root.val, root.property⟩
  rw [completeHost_count hr hM root.property (by omega) (by omega) hN]
  exact completeHostFormula_pos hr (by omega) hN
end LooseHamilton
