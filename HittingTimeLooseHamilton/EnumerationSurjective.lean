module

public import HittingTimeLooseHamilton.DecodeEncode

public section

/-! The complete-host data decode onto the actual family of unoriented cycles. -/
noncomputable section
open Finset
namespace LooseHamilton.CompleteHostCode
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {r k : ℕ} {markers : Finset (Finset V)} {root : Finset V}

/-- Decode data as an actual member of the unrestricted complete-host cycle family. -/
@[expose] def decodeFamily (hM : IsPairMatching markers) (hroot : root ∈ markers)
    (hr : 3 ≤ r) (hk : 3 ≤ k) (hsk : markers.card ≤ k)
    (c : CompleteHostCode r k markers root) :
    ↥(unrestrictedCycleFamily r markers (completeEdges V r)) := by
  refine ⟨decodeEdges hM hroot hk hsk c, ?_⟩
  rw [mem_unrestrictedCycleFamily _ _ _ _ hr]
  refine ⟨decode_isMixedCycle hM hroot hr hk hsk c, ?_⟩
  intro e he
  rw [mem_completeEdges]
  exact (decode_isMixedCycle hM hroot hr hk hsk c).uniform hr e he

/-- Every actual complete-host cycle is obtained from its normalized block data. -/
theorem decodeFamily_surjective (hM : IsPairMatching markers) (hroot : root ∈ markers)
    (hr : 3 ≤ r) (hk : 3 ≤ k) (hsk : markers.card ≤ k)
    (hN : Fintype.card V = (r - 1) * k + markers.card) :
    Function.Surjective (decodeFamily hM hroot hr hk hsk) := by
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
  exact C.decode_encode hM ⟨root, hroot⟩ hk
    (hC.some.normalize_markerStart ⟨root, hroot⟩ (rootEndpoint hM root hroot))

end LooseHamilton.CompleteHostCode
