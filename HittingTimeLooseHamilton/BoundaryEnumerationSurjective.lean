module

public import HittingTimeLooseHamilton.BoundaryDecodeEncode

public section

/-! Two-edge extension of the existing enumeration construction.
The original three-edge modules remain unchanged and their compiled lemmas are reused. -/

/-! The complete-host data decode onto the actual family of unoriented cycles. -/
noncomputable section
open Finset
namespace LooseHamilton.CompleteHostCode
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {r k : ℕ} {markers : Finset (Finset V)} {root : Finset V}

/-- Decode data as an actual member of the unrestricted complete-host cycle family. -/
@[expose] def decodeFamily_ge_two (hM : IsPairMatching markers) (hroot : root ∈ markers)
    (hr : 3 ≤ r) (hk : 2 ≤ k) (hsk : markers.card ≤ k)
    (c : CompleteHostCode r k markers root) :
    ↥(unrestrictedCycleFamily r markers (completeEdges V r)) := by
  refine ⟨decodeEdges_ge_two hM hroot hk hsk c, ?_⟩
  rw [mem_unrestrictedCycleFamily _ _ _ _ hr]
  refine ⟨decode_isMixedCycle_ge_two hM hroot hr hk hsk c, ?_⟩
  intro e he
  rw [mem_completeEdges]
  exact (decode_isMixedCycle_ge_two hM hroot hr hk hsk c).uniform hr e he

/-- Every actual complete-host cycle is obtained from its normalized block data. -/
theorem decodeFamily_surjective_ge_two (hM : IsPairMatching markers) (hroot : root ∈ markers)
    (hr : 3 ≤ r) (hk : 2 ≤ k) (hsk : markers.card ≤ k)
    (hN : Fintype.card V = (r - 1) * k + markers.card) :
    Function.Surjective (decodeFamily_ge_two hM hroot hr hk hsk) := by
  rintro ⟨E, hE⟩
  have hC := ((mem_unrestrictedCycleFamily _ _ _ _ hr).mp hE).1
  have hcard : E.card = k := by
    apply Nat.mul_left_cancel (show 0 < r - 1 by omega)
    have h := (hC.vertex_card hr).symm.trans hN
    omega
  subst k
  let C := hC.some.normalize ⟨root, hroot⟩ (rootEndpoint hM root hroot)
  refine ⟨C.toCompleteHostCode root, ?_⟩
  apply Subtype.ext
  exact C.decode_encode_ge_two hM ⟨root, hroot⟩ hk
    (hC.some.normalize_markerStart ⟨root, hroot⟩ (rootEndpoint hM root hroot))

end LooseHamilton.CompleteHostCode
