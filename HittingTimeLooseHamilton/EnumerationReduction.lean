module

public import HittingTimeLooseHamilton.EnumerationCodes

public section

/-! # Reduction of Proposition 2.2 to the two actual decoder equivalences
No equivalence is assumed as an axiom. The arguments of these conditional
lemmas remain explicit until the combinatorial construction supplies them.
-/
noncomputable section
namespace LooseHamilton
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- An actual equivalence to the edge-set family gives the unrestricted formula. -/
theorem completeHostCount_of_equiv {r k : ℕ} {markers : Finset (Finset V)}
    {root : Finset V} (hr : 3 ≤ r) (hM : IsPairMatching markers)
    (hroot : root ∈ markers) (hsk : markers.card ≤ k)
    (hN : Fintype.card V = (r - 1) * k + markers.card)
    (e : CompleteHostCode r k markers root ≃
      ↥(unrestrictedCycleFamily r markers (completeEdges V r))) :
    unrestrictedCycleCount r markers (completeEdges V r) =
      completeHostFormula r (Fintype.card V) k markers.card := by
  have hc := Fintype.card_congr e
  rw [completeHostCode_card hr hM hroot hsk hN, Fintype.card_coe] at hc
  exact hc.symm

/-- Both actual family equivalences are required for the restriction formula. -/
theorem allowedHostCount_of_equivs {r k : ℕ} {markers : Finset (Finset V)}
    {root : Finset V} (hr : 3 ≤ r) (hM : IsPairMatching markers)
    (hroot : root ∈ markers) (hks : 2 * markers.card ≤ k)
    (hN : Fintype.card V = (r - 1) * k + markers.card)
    (e : CompleteHostCode r k markers root ≃
      ↥(unrestrictedCycleFamily r markers (completeEdges V r)))
    (a : AllowedHostCode r k markers root ≃
      ↥(cycleFamily r markers (completeEdges V r) (originalPorts markers))) :
    (cycleCount r markers (completeEdges V r) (originalPorts markers) : ℝ) =
      (unrestrictedCycleCount r markers (completeEdges V r) : ℝ) *
        prohibitionRatio k markers.card := by
  have he := Fintype.card_congr e
  have ha := Fintype.card_congr a
  rw [Fintype.card_coe] at he ha
  unfold cycleCount unrestrictedCycleCount FiniteFamily.count
  rw [← ha, ← he]
  exact allowedHostCode_card_ratio hr hM hroot hks hN

end LooseHamilton
