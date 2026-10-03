module

public import HittingTimeLooseHamilton.BoundaryEnumerationSurjective
public import HittingTimeLooseHamilton.BoundaryDecodeInjective
public import HittingTimeLooseHamilton.EnumerationReduction

public section

/-! Complete-host enumeration also holds with two ordinary edges when a marked
edge is present. The expanded mixed cycle has at least three edges. This extension
is required after contracting an edge in the smallest case of Proposition 2.4. -/
noncomputable section
namespace LooseHamilton
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Exact correspondence between complete-host data and actual unoriented cycles. -/
@[expose] def completeHostEnumerationEquiv_ge_two {r k : ℕ} {markers : Finset (Finset V)}
    {root : Finset V} (hr : 3 ≤ r) (hM : IsPairMatching markers)
    (hroot : root ∈ markers) (hk : 2 ≤ k) (hsk : markers.card ≤ k)
    (hN : Fintype.card V = (r - 1) * k + markers.card) :
    CompleteHostCode r k markers root ≃
      ↥(unrestrictedCycleFamily r markers (completeEdges V r)) :=
  Equiv.ofBijective (CompleteHostCode.decodeFamily_ge_two hM hroot hr hk hsk)
    ⟨fun _ _ h => CompleteHostCode.decodeEdges_injective_ge_two hM hroot hr hk hsk
      (congrArg Subtype.val h),
      CompleteHostCode.decodeFamily_surjective_ge_two hM hroot hr hk hsk hN⟩

@[simp] theorem completeHostEnumerationEquiv_val_ge_two {r k : ℕ} {markers : Finset (Finset V)}
    {root : Finset V} (hr : 3 ≤ r) (hM : IsPairMatching markers)
    (hroot : root ∈ markers) (hk : 2 ≤ k) (hsk : markers.card ≤ k)
    (hN : Fintype.card V = (r - 1) * k + markers.card)
    (c : CompleteHostCode r k markers root) :
    (completeHostEnumerationEquiv_ge_two hr hM hroot hk hsk hN c).val =
      CompleteHostCode.decodeEdges_ge_two hM hroot hk hsk c := rfl

/-- Unrestricted complete-host count, for any finite vertex type. -/
theorem completeHost_count_ge_two {r k : ℕ} {markers : Finset (Finset V)}
    {root : Finset V} (hr : 3 ≤ r) (hM : IsPairMatching markers)
    (hroot : root ∈ markers) (hk : 2 ≤ k) (hsk : markers.card ≤ k)
    (hN : Fintype.card V = (r - 1) * k + markers.card) :
    unrestrictedCycleCount r markers (completeEdges V r) =
      completeHostFormula r (Fintype.card V) k markers.card :=
  completeHostCount_of_equiv hr hM hroot hsk hN
    (completeHostEnumerationEquiv_ge_two hr hM hroot hk hsk hN)


end LooseHamilton
