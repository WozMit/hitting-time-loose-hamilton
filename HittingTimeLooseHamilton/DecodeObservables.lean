module

public import HittingTimeLooseHamilton.CompleteHostDecode

public section
noncomputable section
open Finset
namespace LooseHamilton.CompleteHostCode
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {r k : ℕ} {markers : Finset (Finset V)} {root : Finset V}

theorem decode_junctions (hM : IsPairMatching markers) (hroot : root ∈ markers)
    (hr : 3 ≤ r) (hk : 3 ≤ k) (hsk : markers.card ≤ k)
    (c : CompleteHostCode r k markers root) :
    univ.image (decodeWitness hM hroot hr hk hsk c).junction =
      originalPorts markers ∪ c.1.val := by
  change univ.image (decodeData hM hroot hk hsk c).expanded.junction = _
  rw [PermutationCycleData.expanded_junction_image]
  exact codeJunction_image hM hroot c.2.1 c.1

theorem decode_markerStart (hM : IsPairMatching markers) (hroot : root ∈ markers)
    (hr : 3 ≤ r) (hk : 3 ≤ k) (hsk : markers.card ≤ k)
    (c : CompleteHostCode r k markers root) (e : ↥markers) :
    (decodeWitness hM hroot hr hk hsk c).markerStart e =
      markerFirst hM root hroot c.2.1 e := by
  apply Subtype.ext
  change (decodeData hM hroot hk hsk c).expanded.junction
    ((decodeData hM hroot hk hsk c).expanded.slot.symm (.inl e)) = _
  rw [PermutationCycleData.expanded_marker_start]
  rfl

theorem decode_root_start (hM : IsPairMatching markers) (hroot : root ∈ markers)
    (hr : 3 ≤ r) (hk : 3 ≤ k) (hsk : markers.card ≤ k)
    (c : CompleteHostCode r k markers root) :
    (decodeWitness hM hroot hr hk hsk c).markerStart ⟨root, hroot⟩ =
      rootEndpoint hM root hroot := by
  rw [decode_markerStart, markerFirst_root]

theorem decode_markerDirections (hM : IsPairMatching markers) (hroot : root ∈ markers)
    (hr : 3 ≤ r) (hk : 3 ≤ k) (hsk : markers.card ≤ k)
    (c : CompleteHostCode r k markers root) :
    (decodeWitness hM hroot hr hk hsk c).markerDirections root = c.2.1 := by
  funext e
  exact (decode_markerStart hM hroot hr hk hsk c
    ⟨e.val, mem_of_mem_erase e.property⟩).trans
      (markerFirst_nonroot hM root hroot c.2.1 e)

theorem decode_ordinaryJunctions (hM : IsPairMatching markers) (hroot : root ∈ markers)
    (hr : 3 ≤ r) (hk : 3 ≤ k) (hsk : markers.card ≤ k)
    (c : CompleteHostCode r k markers root) :
    (decodeWitness hM hroot hr hk hsk c).ordinaryJunctionChoice.val = c.1.val := by
  change (univ.image (decodeWitness hM hroot hr hk hsk c).junction \ originalPorts markers) = _
  rw [decode_junctions]
  have hJ := ((mem_ordinaryJunctionChoices _ _ _).mp c.1.property).1
  ext v
  constructor
  · intro hv
    obtain ⟨hv, hn⟩ := mem_sdiff.mp hv
    exact (mem_union.mp hv).resolve_left hn
  · intro hv
    exact mem_sdiff.mpr ⟨mem_union_right _ hv, (mem_sdiff.mp (hJ hv)).2⟩
end LooseHamilton.CompleteHostCode
