module

public import HittingTimeLooseHamilton.DecodeObservables
public import HittingTimeLooseHamilton.WitnessDecoderFacts
public import HittingTimeLooseHamilton.ContractedEndpoints
public import HittingTimeLooseHamilton.AllowedCycles

public section
noncomputable section
open Finset
namespace LooseHamilton.CompleteHostCode
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {r k : ℕ} {markers : Finset (Finset V)} {root : Finset V}
variable (hM : IsPairMatching markers) (hroot : root ∈ markers)
  (hr : 3 ≤ r) (hk : 3 ≤ k) (hsk : markers.card ≤ k)
  (c : CompleteHostCode r k markers root)

@[expose] def decodedBlockEquiv : (↥markers ⊕ ↥c.1.val) ≃
    (decodeWitness hM hroot hr hk hsk c).ContractedBlock :=
  Equiv.sumCongr (Equiv.refl _) (Equiv.subtypeEquivRight (fun v => by
    rw [decode_ordinaryJunctions hM hroot hr hk hsk c]))

theorem decoded_blockStart (b : ↥markers ⊕ ↥c.1.val) :
    (decodeWitness hM hroot hr hk hsk c).blockStart
      (decodedBlockEquiv hM hroot hr hk hsk c b) =
      codeJunction hM hroot c.2.1 c.1 (.inl b) := by
  cases b with
  | inl m => exact congrArg Subtype.val (decode_markerStart hM hroot hr hk hsk c m)
  | inr v => rfl

theorem decoded_blockEnd (b : ↥markers ⊕ ↥c.1.val) :
    (decodeWitness hM hroot hr hk hsk c).blockEnd
      (decodedBlockEquiv hM hroot hr hk hsk c b) =
      codeJunction hM hroot c.2.1 c.1 (blockLast b) := by
  cases b with
  | inl m =>
    change ((decodeData hM hroot hk hsk c).witness hr).junction
      (finRotate _ (((decodeData hM hroot hk hsk c).witness hr).slot.symm (.inl m))) = _
    rw [PermutationCycleData.witness_marker_end]
    change codeJunction hM hroot c.2.1 c.1
      (BlockEnumeration.gapNext _ (markerEmbedding markers ↥c.1.val)
        (.inl (markerEmbedding markers ↥c.1.val m))) = _
    rw [BlockEnumeration.gapNext_gap]
    rfl
  | inr v => rfl

theorem decoded_outgoingEdge (b : ↥markers ⊕ ↥c.1.val) :
    (decodeWitness hM hroot hr hk hsk c).outgoingEdge
      (decodedBlockEquiv hM hroot hr hk hsk c b) =
      (decodeData hM hroot hk hsk c).expanded.edgeEquiv hr b := by
  let C := decodeWitness hM hroot hr hk hsk c
  apply Sum.inr_injective
  rw [← C.slot_outgoingEdge]
  apply C.slot.symm.injective
  rw [C.slot.symm_apply_apply]
  apply C.junction_injective
  rw [← C.blockEnd_eq, decoded_blockEnd]
  symm
  exact ((decodeData hM hroot hk hsk c).witness_ordinary_start hr b).trans (by cases b <;> rfl)

@[expose] def decodeOrder (hk₀ : 3 ≤ k) (hsk₀ : markers.card ≤ k)
    (c₀ : CompleteHostCode r k markers root) : Equiv.Perm (↥markers ⊕ ↥c₀.1.val) :=
  permutationTransport (codeBlockLabels markers k hsk₀ c₀.1).symm
    (rootedOrderCycleEquiv k (Nat.lt_of_lt_of_le (by decide : 0 < 3) hk₀) c₀.2.2.1).val

theorem decoded_blockSuccessor (b : ↥markers ⊕ ↥c.1.val) :
    (decodeWitness hM hroot hr hk hsk c).blockSuccessor
      (decodedBlockEquiv hM hroot hr hk hsk c b) =
      decodedBlockEquiv hM hroot hr hk hsk c (decodeOrder hk hsk c b) := by
  let C := decodeWitness hM hroot hr hk hsk c
  let E := decodedBlockEquiv hM hroot hr hk hsk c
  have hstart (x : C.ContractedBlock) :
      C.blockStart x = codeJunction hM hroot c.2.1 c.1 (.inl (E.symm x)) := by
    simpa only [E, Equiv.apply_symm_apply] using decoded_blockStart hM hroot hr hk hsk c (E.symm x)
  have hinj : Function.Injective C.blockStart := by
    intro x y h
    rw [hstart, hstart] at h
    exact E.symm.injective (Sum.inl_injective ((codeJunction hM hroot c.2.1 c.1).injective h))
  apply hinj
  rw [C.blockSuccessor_start]
  rw [← C.ordinary_slot_index, decoded_outgoingEdge]
  trans (decodeData hM hroot hk hsk c).junction
    ((decodeData hM hroot hk hsk c).successor ((decodeData hM hroot hk hsk c).slot.symm (.inr b)))
  · exact (decodeData hM hroot hk hsk c).witness_ordinary_end hr b
  rw [decoded_blockStart]
  have hs : (blockSlot markers ↥c.1.val).symm (.inr b) = blockLast b := by cases b <;> rfl
  change codeJunction hM hroot c.2.1 c.1
    (BlockEnumeration.gapPermutation (decodeOrder hk hsk c)
      (markerEmbedding markers ↥c.1.val) ((blockSlot markers ↥c.1.val).symm (.inr b))) = _
  rw [hs]
  exact congrArg (codeJunction hM hroot c.2.1 c.1) (blockLast_successor _ b)

theorem decoded_privateBlock (b : ↥markers ⊕ ↥c.1.val) :
    (decodeWitness hM hroot hr hk hsk c).privateBlock
      ((decodeWitness hM hroot hr hk hsk c).outgoingEdge
        (decodedBlockEquiv hM hroot hr hk hsk c b)) =
      Allocation.liftBlocks c.2.2.2 ⟨Subtype.val, Subtype.val_injective⟩
        (codeBlockLabels markers k hsk c.1) b := by
  rw [decoded_outgoingEdge]
  exact (decodeData hM hroot hk hsk c).witness_privateBlock hr b

theorem decoded_next_junction (b : ↥markers ⊕ ↥c.1.val) :
    (decodeWitness hM hroot hr hk hsk c).junction
      (finRotate (decodeWitness hM hroot hr hk hsk c).length
        ((decodeWitness hM hroot hr hk hsk c).outgoingSlot
          (decodedBlockEquiv hM hroot hr hk hsk c b))) =
      codeJunction hM hroot c.2.1 c.1 (.inl (decodeOrder hk hsk c b)) := by
  rw [← MixedCycleWitness.blockSuccessor_start, decoded_blockSuccessor, decoded_blockStart]
end LooseHamilton.CompleteHostCode
