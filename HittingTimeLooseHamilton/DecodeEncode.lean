module

public import HittingTimeLooseHamilton.EncodedEndpoints
public import HittingTimeLooseHamilton.AllowedCycles

public section
noncomputable section
open Finset
namespace LooseHamilton.MixedCycleWitness
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {r : ℕ} {markers edges : Finset (Finset V)}

theorem encoded_blockOrder (C : MixedCycleWitness r markers edges) (root : Finset V) :
    CompleteHostCode.blockOrder C.markers_card_le_edges_card C.edges_card_pos
      (C.toCompleteHostCode root) = C.blockSuccessor := by
  let labels := codeBlockLabels markers edges.card C.markers_card_le_edges_card C.ordinaryJunctionChoice
  let σ : BlockEnumeration.FullCycle (Fin edges.card) :=
    ⟨permutationTransport labels C.blockSuccessor,
      permutationTransport_cycle _ _ C.blockSuccessor_cycle⟩
  have h := congrArg (fun z : BlockEnumeration.FullCycle (Fin edges.card) =>
    permutationTransport labels.symm z.val)
    ((rootedOrderCycleEquiv edges.card C.edges_card_pos).apply_symm_apply σ)
  refine h.trans ?_
  ext b
  change labels.symm (labels (C.blockSuccessor (labels.symm (labels b)))) = _
  simp only [Equiv.symm_apply_apply]

theorem lifted_privateAllocation (C : MixedCycleWitness r markers edges) {k : ℕ}
    (labels : C.ContractedBlock ≃ Fin k) (b : C.ContractedBlock) :
    Allocation.liftBlocks (C.privateAllocation labels) ⟨Subtype.val, Subtype.val_injective⟩ labels b =
      C.privateBlock (C.outgoingEdge b) := by
  ext v
  simp only [Allocation.liftBlocks, mem_map]
  constructor
  · rintro ⟨u, hu, rfl⟩
    simp only [C.mem_privateAllocation, Equiv.symm_apply_apply] at hu
    exact hu
  · intro hv
    let u : PrivatePool markers C.ordinaryJunctionChoice.val :=
      ⟨v, C.private_mem_pool _ hv⟩
    refine ⟨u, ?_, rfl⟩
    rw [C.mem_privateAllocation, Equiv.symm_apply_apply]
    exact hv

theorem encoded_codeJunction_start (C : MixedCycleWitness r markers edges)
    (hM : IsPairMatching markers) (root : ↥markers)
    (hroot : C.markerStart root = rootEndpoint hM root.val root.property)
    (b : C.ContractedBlock) :
    codeJunction hM root.property (C.markerDirections root.val) C.ordinaryJunctionChoice (.inl b) =
      C.blockStart b := by
  cases b with
  | inl m => exact congrArg Subtype.val (C.encoded_markerFirst hM root hroot m)
  | inr v => rfl

theorem encoded_codeJunction_end (C : MixedCycleWitness r markers edges)
    (hM : IsPairMatching markers) (root : ↥markers)
    (hroot : C.markerStart root = rootEndpoint hM root.val root.property)
    (b : C.ContractedBlock) :
    codeJunction hM root.property (C.markerDirections root.val) C.ordinaryJunctionChoice (blockLast b) =
      C.blockEnd b := by
  cases b with
  | inl m => exact C.encoded_markerLast hM root hroot m
  | inr v => rfl

/-- Decoding an encoded, normalized presentation recovers each of its ordinary edges. -/
theorem decode_encode_edge (C : MixedCycleWitness r markers edges)
    (hM : IsPairMatching markers) (root : ↥markers) (hk : 3 ≤ edges.card)
    (hroot : C.markerStart root = rootEndpoint hM root.val root.property)
    (b : C.ContractedBlock) :
    (CompleteHostCode.decodeData hM root.property hk C.markers_card_le_edges_card
      (C.toCompleteHostCode root.val)).expanded.edge b = (C.outgoingEdge b).val := by
  refine (decodeBlockData_edge hM root.property _ _ _ _
    (permutationTransport_cycle _ _
      (rootedOrderCycleEquiv edges.card C.edges_card_pos (C.toCompleteHostCode root.val).2.2.1).property)
    _ _ b).trans ?_
  change {codeJunction hM root.property (C.markerDirections root.val) C.ordinaryJunctionChoice (blockLast b),
      codeJunction hM root.property (C.markerDirections root.val) C.ordinaryJunctionChoice
        (.inl (CompleteHostCode.blockOrder C.markers_card_le_edges_card C.edges_card_pos
          (C.toCompleteHostCode root.val) b))} ∪
      Allocation.liftBlocks (C.privateAllocation (codeBlockLabels markers edges.card
        C.markers_card_le_edges_card C.ordinaryJunctionChoice))
        ⟨Subtype.val, Subtype.val_injective⟩
        (codeBlockLabels markers edges.card C.markers_card_le_edges_card C.ordinaryJunctionChoice) b = _
  have hb := congrArg (fun σ : Equiv.Perm C.ContractedBlock =>
    codeJunction hM root.property (C.markerDirections root.val) C.ordinaryJunctionChoice
      (.inl (σ b))) (C.encoded_blockOrder root.val)
  have hs := hb.trans (C.encoded_codeJunction_start hM root hroot (C.blockSuccessor b))
  have he := C.encoded_codeJunction_end hM root hroot b
  have hp := C.lifted_privateAllocation
    (codeBlockLabels markers edges.card C.markers_card_le_edges_card C.ordinaryJunctionChoice) b
  exact (congrArg₂ (fun A B : Finset V => A ∪ B)
    (congrArg₂ (fun x y : V => ({x,y} : Finset V)) he hs) hp).trans
    (C.outgoingEdge_formula b).symm

/-- The first roundtrip: the finite data reconstructs the original unoriented cycle. -/
theorem decode_encode (C : MixedCycleWitness r markers edges)
    (hM : IsPairMatching markers) (root : ↥markers) (hk : 3 ≤ edges.card)
    (hroot : C.markerStart root = rootEndpoint hM root.val root.property) :
    CompleteHostCode.decodeEdges hM root.property hk C.markers_card_le_edges_card
      (C.toCompleteHostCode root.val) = edges := by
  ext e
  change e ∈ univ.image _ ↔ e ∈ edges
  simp only [mem_image, mem_univ, true_and]
  constructor
  · rintro ⟨b, hb⟩
    have heq := (C.decode_encode_edge hM root hk hroot b).symm.trans hb
    exact heq ▸ (C.outgoingEdge b).property
  · intro he
    refine ⟨C.blockEdgeEquiv.symm ⟨e, he⟩, ?_⟩
    exact (C.decode_encode_edge hM root hk hroot _).trans
      (congrArg Subtype.val (C.blockEdgeEquiv.apply_symm_apply ⟨e, he⟩))

end LooseHamilton.MixedCycleWitness
