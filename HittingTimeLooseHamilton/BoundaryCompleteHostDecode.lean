module

public import HittingTimeLooseHamilton.DecodeCycle
public import HittingTimeLooseHamilton.WitnessEncoding

public section

/-! Two-edge extension of the existing enumeration construction.
The original three-edge modules remain unchanged and their compiled lemmas are reused. -/
noncomputable section
namespace LooseHamilton.CompleteHostCode
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {r k : ℕ} {markers : Finset (Finset V)} {root : Finset V}

/-- Decode the cyclic block order, orientations, and unordered private allocations. -/
@[expose] def decodeData_ge_two (hM : IsPairMatching markers) (hroot : root ∈ markers)
    (hk : 2 ≤ k) (hsk : markers.card ≤ k) (c : CompleteHostCode r k markers root) :
    PermutationCycleData r markers (BlockJunctions markers ↥c.1.val)
      (↥markers ⊕ ↥c.1.val) := by
  let b := codeBlockLabels markers k hsk c.1
  let σ := rootedOrderCycleEquiv k (by omega) c.2.2.1
  have hc : 3 ≤ Fintype.card (BlockJunctions markers ↥c.1.val) := by
    change 3 ≤ Fintype.card ((↥markers ⊕ ↥c.1.val) ⊕ ↥markers)
    rw [Fintype.card_sum]
    have hb : Fintype.card (↥markers ⊕ ↥c.1.val) = k := by
      simpa using Fintype.card_congr b
    rw [hb, Fintype.card_coe]
    have hm := Finset.card_pos.mpr ⟨root, hroot⟩
    omega
  exact decodeBlockData hM hroot c.1 c.2.1 b
    (permutationTransport b.symm σ.val) (permutationTransport_cycle _ _ σ.property) hc c.2.2.2

@[expose] def decodeEdges_ge_two (hM : IsPairMatching markers) (hroot : root ∈ markers)
    (hk : 2 ≤ k) (hsk : markers.card ≤ k) (c : CompleteHostCode r k markers root) :
    Finset (Finset V) := (decodeData_ge_two hM hroot hk hsk c).expanded.edges

@[expose] def decodeWitness_ge_two (hM : IsPairMatching markers) (hroot : root ∈ markers)
    (hr : 3 ≤ r) (hk : 2 ≤ k) (hsk : markers.card ≤ k)
    (c : CompleteHostCode r k markers root) :
    MixedCycleWitness r markers (decodeEdges_ge_two hM hroot hk hsk c) :=
  (decodeData_ge_two hM hroot hk hsk c).witness hr

theorem decode_isMixedCycle_ge_two (hM : IsPairMatching markers) (hroot : root ∈ markers)
    (hr : 3 ≤ r) (hk : 2 ≤ k) (hsk : markers.card ≤ k)
    (c : CompleteHostCode r k markers root) :
    IsMixedCycle r markers (decodeEdges_ge_two hM hroot hk hsk c) :=
  ⟨decodeWitness_ge_two hM hroot hr hk hsk c⟩

theorem decode_edges_card_ge_two (hM : IsPairMatching markers) (hroot : root ∈ markers)
    (hr : 3 ≤ r) (hk : 2 ≤ k) (hsk : markers.card ≤ k)
    (c : CompleteHostCode r k markers root) :
    (decodeEdges_ge_two hM hroot hk hsk c).card = k := by
  rw [decodeEdges_ge_two, ExpandedCycleData.edges_card _ hr]
  simpa using Fintype.card_congr (codeBlockLabels markers k hsk c.1)
end LooseHamilton.CompleteHostCode
