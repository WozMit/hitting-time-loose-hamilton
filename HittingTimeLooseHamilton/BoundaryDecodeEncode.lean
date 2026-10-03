module

public import HittingTimeLooseHamilton.DecodeEncode
public import HittingTimeLooseHamilton.BoundaryCompleteHostDecode

public section

/-! Two-edge extension of the existing enumeration construction.
The original three-edge modules remain unchanged and their compiled lemmas are reused. -/
noncomputable section
open Finset
namespace LooseHamilton.MixedCycleWitness
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {r : ℕ} {markers edges : Finset (Finset V)}

theorem decode_encode_edge_ge_two (C : MixedCycleWitness r markers edges)
    (hM : IsPairMatching markers) (root : ↥markers) (hk : 2 ≤ edges.card)
    (hroot : C.markerStart root = rootEndpoint hM root.val root.property)
    (b : C.ContractedBlock) :
    (CompleteHostCode.decodeData_ge_two hM root.property hk C.markers_card_le_edges_card
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
theorem decode_encode_ge_two (C : MixedCycleWitness r markers edges)
    (hM : IsPairMatching markers) (root : ↥markers) (hk : 2 ≤ edges.card)
    (hroot : C.markerStart root = rootEndpoint hM root.val root.property) :
    CompleteHostCode.decodeEdges_ge_two hM root.property hk C.markers_card_le_edges_card
      (C.toCompleteHostCode root.val) = edges := by
  ext e
  change e ∈ univ.image _ ↔ e ∈ edges
  simp only [mem_image, mem_univ, true_and]
  constructor
  · rintro ⟨b, hb⟩
    have heq := (C.decode_encode_edge_ge_two hM root hk hroot b).symm.trans hb
    exact heq ▸ (C.outgoingEdge b).property
  · intro he
    refine ⟨C.blockEdgeEquiv.symm ⟨e, he⟩, ?_⟩
    exact (C.decode_encode_edge_ge_two hM root hk hroot _).trans
      (congrArg Subtype.val (C.blockEdgeEquiv.apply_symm_apply ⟨e, he⟩))

end LooseHamilton.MixedCycleWitness
