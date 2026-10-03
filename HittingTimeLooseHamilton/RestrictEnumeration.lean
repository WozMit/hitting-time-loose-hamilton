module

public import HittingTimeLooseHamilton.AllowedCodes
public import HittingTimeLooseHamilton.AllowedCycles

public section

/-! Restricting an actual complete-host enumeration equivalence to the fixed port prohibition.
The unrestricted equivalence is an explicit input here; it is not supplied by code counts. -/
noncomputable section
namespace LooseHamilton
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Both code-level predicates name exactly the same decoded block permutation. -/
theorem codeSeparated_iff_hasSeparatedMarkers {r k : ℕ}
    {markers : Finset (Finset V)} {root : Finset V}
    (hk : 0 < k) (hsk : markers.card ≤ k) (c : CompleteHostCode r k markers root) :
    codeSeparated hk hsk c ↔ CompleteHostCode.HasSeparatedMarkers hsk hk c := Iff.rfl

/-- Restrict an unrestricted cycle family by its actual edge prohibition. -/
@[expose] def restrictCycleFamilyEquiv {r : ℕ} (hr : 3 ≤ r)
    (markers host : Finset (Finset V)) (ports : Finset V) :
    {C : ↥(unrestrictedCycleFamily r markers host) // C.val ⊆ allowedEdges r ports} ≃
      ↥(cycleFamily r markers host ports) where
  toFun C := ⟨C.val.val, (mem_cycleFamily _ _ _ _ _).mpr
    ⟨((mem_unrestrictedCycleFamily _ _ _ _ hr).mp C.val.property).1,
      ((mem_unrestrictedCycleFamily _ _ _ _ hr).mp C.val.property).2, C.property⟩⟩
  invFun C := ⟨⟨C.val, (mem_unrestrictedCycleFamily _ _ _ _ hr).mpr
    ⟨((mem_cycleFamily _ _ _ _ _).mp C.property).1,
      ((mem_cycleFamily _ _ _ _ _).mp C.property).2.1⟩⟩,
    ((mem_cycleFamily _ _ _ _ _).mp C.property).2.2⟩
  left_inv C := by apply Subtype.ext; apply Subtype.ext; rfl
  right_inv C := by apply Subtype.ext; rfl

/-- Once unrestricted decoding is bijective, its restriction is precisely the allowed family. -/
@[expose] def allowedHostEnumerationEquiv {r k : ℕ} {markers : Finset (Finset V)}
    {root : Finset V} (hr : 3 ≤ r) (hM : IsPairMatching markers)
    (hroot : root ∈ markers) (hk : 3 ≤ k) (hsk : markers.card < k)
    (e : CompleteHostCode r k markers root ≃
      ↥(unrestrictedCycleFamily r markers (completeEdges V r)))
    (he : ∀ c, (e c).val = CompleteHostCode.decodeEdges hM hroot hk hsk.le c) :
    AllowedHostCode r k markers root ≃
      ↥(cycleFamily r markers (completeEdges V r) (originalPorts markers)) :=
  (allowedHostCodeEquiv hsk).trans
    ((e.subtypeEquiv (by
      intro c
      change codeSeparated (by omega) hsk.le c ↔
        (e c).val ⊆ allowedEdges r (originalPorts markers)
      rw [he c, codeSeparated_iff_hasSeparatedMarkers]
      exact (CompleteHostCode.decodeEdges_allowed_iff hr hM hroot hk hsk.le c).symm)).trans
    (restrictCycleFamilyEquiv hr markers (completeEdges V r) (originalPorts markers)))

/-- The restriction ratio transferred to actual cycle counts, with the unrestricted
code/edge-set equivalence as the sole remaining enumeration input. -/
theorem allowed_cycle_count_of_equiv {r k : ℕ} {markers : Finset (Finset V)}
    {root : Finset V} (hr : 3 ≤ r) (hM : IsPairMatching markers)
    (hroot : root ∈ markers) (hk : 3 ≤ k) (hks : 2 * markers.card ≤ k)
    (hN : Fintype.card V = (r - 1) * k + markers.card)
    (e : CompleteHostCode r k markers root ≃
      ↥(unrestrictedCycleFamily r markers (completeEdges V r)))
    (he : ∀ c, (e c).val = CompleteHostCode.decodeEdges hM hroot hk (by omega) c) :
    (cycleCount r markers (completeEdges V r) (originalPorts markers) : ℝ) =
      (unrestrictedCycleCount r markers (completeEdges V r) : ℝ) *
        prohibitionRatio k markers.card := by
  have hs : 0 < markers.card := Finset.card_pos.mpr ⟨root, hroot⟩
  have hsk : markers.card < k := by omega
  have hc := Fintype.card_congr
    (allowedHostEnumerationEquiv hr hM hroot hk hsk e he)
  have hu := Fintype.card_congr e
  simp only [Fintype.card_coe] at hc hu
  change ((cycleFamily r markers (completeEdges V r) (originalPorts markers)).card : ℝ) =
    ((unrestrictedCycleFamily r markers (completeEdges V r)).card : ℝ) * _
  rw [← hc, ← hu]
  exact allowedHostCode_card_ratio hr hM hroot hks hN

end LooseHamilton
