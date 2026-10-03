module

public import HittingTimeLooseHamilton.EnumerationSurjective
public import HittingTimeLooseHamilton.DecodeInjective
public import HittingTimeLooseHamilton.EnumerationReduction
public import HittingTimeLooseHamilton.RestrictEnumeration
public import HittingTimeLooseHamilton.ProhibitionBound

public section

/-! # Proposition 2.2: complete-host enumeration

The finite data are identified with the actual unoriented edge-set family by the
explicit decoder, its reconstruction theorem, and its injectivity. Restriction
to separated marked blocks gives the prescribed original-port prohibition.
-/
noncomputable section
namespace LooseHamilton
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Exact correspondence between complete-host data and actual unoriented cycles. -/
@[expose] def completeHostEnumerationEquiv {r k : ℕ} {markers : Finset (Finset V)}
    {root : Finset V} (hr : 3 ≤ r) (hM : IsPairMatching markers)
    (hroot : root ∈ markers) (hk : 3 ≤ k) (hsk : markers.card ≤ k)
    (hN : Fintype.card V = (r - 1) * k + markers.card) :
    CompleteHostCode r k markers root ≃
      ↥(unrestrictedCycleFamily r markers (completeEdges V r)) :=
  Equiv.ofBijective (CompleteHostCode.decodeFamily hM hroot hr hk hsk)
    ⟨fun _ _ h => CompleteHostCode.decodeEdges_injective hM hroot hr hk hsk
      (congrArg Subtype.val h),
      CompleteHostCode.decodeFamily_surjective hM hroot hr hk hsk hN⟩

@[simp] theorem completeHostEnumerationEquiv_val {r k : ℕ} {markers : Finset (Finset V)}
    {root : Finset V} (hr : 3 ≤ r) (hM : IsPairMatching markers)
    (hroot : root ∈ markers) (hk : 3 ≤ k) (hsk : markers.card ≤ k)
    (hN : Fintype.card V = (r - 1) * k + markers.card)
    (c : CompleteHostCode r k markers root) :
    (completeHostEnumerationEquiv hr hM hroot hk hsk hN c).val =
      CompleteHostCode.decodeEdges hM hroot hk hsk c := rfl

/-- Unrestricted complete-host count, for any finite vertex type. -/
theorem completeHost_count {r k : ℕ} {markers : Finset (Finset V)}
    {root : Finset V} (hr : 3 ≤ r) (hM : IsPairMatching markers)
    (hroot : root ∈ markers) (hk : 3 ≤ k) (hsk : markers.card ≤ k)
    (hN : Fintype.card V = (r - 1) * k + markers.card) :
    unrestrictedCycleCount r markers (completeEdges V r) =
      completeHostFormula r (Fintype.card V) k markers.card :=
  completeHostCount_of_equiv hr hM hroot hsk hN
    (completeHostEnumerationEquiv hr hM hroot hk hsk hN)

/-- The exact restriction ratio for the original marked ports. -/
theorem allowedHost_count {r k : ℕ} {markers : Finset (Finset V)}
    {root : Finset V} (hr : 3 ≤ r) (hM : IsPairMatching markers)
    (hroot : root ∈ markers) (hk : 3 ≤ k) (hks : 2 * markers.card ≤ k)
    (hN : Fintype.card V = (r - 1) * k + markers.card) :
    (cycleCount r markers (completeEdges V r) (originalPorts markers) : ℝ) =
      (unrestrictedCycleCount r markers (completeEdges V r) : ℝ) *
        prohibitionRatio k markers.card :=
  allowed_cycle_count_of_equiv hr hM hroot hk hks hN
    (completeHostEnumerationEquiv hr hM hroot hk (by omega) hN) (fun _ => rfl)

/-- Proposition 2.2 of the manuscript, including both the exact restricted
ratio and its explicit lower bound. -/
theorem proposition22 : Proposition22 := by
  intro r N k s hr hs hk hN markers hM hcard
  have hk3 : 3 ≤ k := le_trans (le_max_left _ _) hk
  have hsk : markers.card ≤ k := by
    rw [hcard]
    exact le_trans (le_max_right _ _) hk
  have hN' : Fintype.card (Fin N) = (r - 1) * k + markers.card := by
    simpa only [Fintype.card_fin, hcard] using hN
  obtain ⟨root, hroot⟩ := Finset.card_pos.mp (show 0 < markers.card by omega)
  constructor
  · simpa only [Fintype.card_fin, hcard] using completeHost_count hr hM hroot hk3 hsk hN'
  · intro hks
    constructor
    · have h := allowedHost_count hr hM hroot hk3 (show 2 * markers.card ≤ k by omega) hN'
      rw [hcard] at h
      simpa only [prohibitionRatio, mul_div_assoc] using h
    · simpa only [prohibitionRatio] using prohibitionRatio_lower hs hks

end LooseHamilton
