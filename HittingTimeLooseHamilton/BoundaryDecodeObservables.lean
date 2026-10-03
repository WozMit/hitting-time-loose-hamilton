module

public import HittingTimeLooseHamilton.BoundaryCompleteHostDecode

public section

/-! Two-edge extension of the existing enumeration construction.
The original three-edge modules remain unchanged and their compiled lemmas are reused. -/
noncomputable section
open Finset
namespace LooseHamilton.CompleteHostCode
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {r k : ℕ} {markers : Finset (Finset V)} {root : Finset V}

theorem decode_junctions_ge_two (hM : IsPairMatching markers) (hroot : root ∈ markers)
    (hr : 3 ≤ r) (hk : 2 ≤ k) (hsk : markers.card ≤ k)
    (c : CompleteHostCode r k markers root) :
    univ.image (decodeWitness_ge_two hM hroot hr hk hsk c).junction =
      originalPorts markers ∪ c.1.val := by
  change univ.image (decodeData_ge_two hM hroot hk hsk c).expanded.junction = _
  rw [PermutationCycleData.expanded_junction_image]
  exact codeJunction_image hM hroot c.2.1 c.1

theorem decode_markerStart_ge_two (hM : IsPairMatching markers) (hroot : root ∈ markers)
    (hr : 3 ≤ r) (hk : 2 ≤ k) (hsk : markers.card ≤ k)
    (c : CompleteHostCode r k markers root) (e : ↥markers) :
    (decodeWitness_ge_two hM hroot hr hk hsk c).markerStart e =
      markerFirst hM root hroot c.2.1 e := by
  apply Subtype.ext
  change (decodeData_ge_two hM hroot hk hsk c).expanded.junction
    ((decodeData_ge_two hM hroot hk hsk c).expanded.slot.symm (.inl e)) = _
  rw [PermutationCycleData.expanded_marker_start]
  rfl

theorem decode_root_start_ge_two (hM : IsPairMatching markers) (hroot : root ∈ markers)
    (hr : 3 ≤ r) (hk : 2 ≤ k) (hsk : markers.card ≤ k)
    (c : CompleteHostCode r k markers root) :
    (decodeWitness_ge_two hM hroot hr hk hsk c).markerStart ⟨root, hroot⟩ =
      rootEndpoint hM root hroot := by
  rw [decode_markerStart_ge_two, markerFirst_root]

theorem decode_markerDirections_ge_two (hM : IsPairMatching markers) (hroot : root ∈ markers)
    (hr : 3 ≤ r) (hk : 2 ≤ k) (hsk : markers.card ≤ k)
    (c : CompleteHostCode r k markers root) :
    (decodeWitness_ge_two hM hroot hr hk hsk c).markerDirections root = c.2.1 := by
  funext e
  exact (decode_markerStart_ge_two hM hroot hr hk hsk c
    ⟨e.val, mem_of_mem_erase e.property⟩).trans
      (markerFirst_nonroot hM root hroot c.2.1 e)

theorem decode_ordinaryJunctions_ge_two (hM : IsPairMatching markers) (hroot : root ∈ markers)
    (hr : 3 ≤ r) (hk : 2 ≤ k) (hsk : markers.card ≤ k)
    (c : CompleteHostCode r k markers root) :
    (decodeWitness_ge_two hM hroot hr hk hsk c).ordinaryJunctionChoice.val = c.1.val := by
  change (univ.image (decodeWitness_ge_two hM hroot hr hk hsk c).junction \ originalPorts markers) = _
  rw [decode_junctions_ge_two]
  have hJ := ((mem_ordinaryJunctionChoices _ _ _).mp c.1.property).1
  ext v
  constructor
  · intro hv
    obtain ⟨hv, hn⟩ := mem_sdiff.mp hv
    exact (mem_union.mp hv).resolve_left hn
  · intro hv
    exact mem_sdiff.mpr ⟨mem_union_right _ hv, (mem_sdiff.mp (hJ hv)).2⟩
end LooseHamilton.CompleteHostCode
