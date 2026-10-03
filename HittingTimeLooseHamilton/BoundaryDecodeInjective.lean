module

public import HittingTimeLooseHamilton.BoundaryDecodeBlockRecovery
public import HittingTimeLooseHamilton.WitnessPhysicalUniqueness
public import HittingTimeLooseHamilton.IntrinsicRoles
public import HittingTimeLooseHamilton.OrientationUniqueness

public section

/-! Two-edge extension of the existing enumeration construction.
The original three-edge modules remain unchanged and their compiled lemmas are reused. -/
noncomputable section
open Finset
namespace LooseHamilton.CompleteHostCode
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {r k : ℕ} {markers : Finset (Finset V)} {root : Finset V}
variable (hM : IsPairMatching markers) (hroot : root ∈ markers)
  (hr : 3 ≤ r) (hk : 2 ≤ k) (hsk : markers.card ≤ k)

include hr in
theorem decode_intrinsic_junctions_ge_two (c : CompleteHostCode r k markers root) :
    ordinaryJunctions markers (decodeEdges_ge_two hM hroot hk hsk c) = c.1.val := by
  rw [ordinaryJunctions, (decodeWitness_ge_two hM hroot hr hk hsk c).cycleJunctions_eq hr]
  exact decode_ordinaryJunctions_ge_two hM hroot hr hk hsk c

include hr in
theorem decode_eq_junction_choice_ge_two {c d : CompleteHostCode r k markers root}
    (he : decodeEdges_ge_two hM hroot hk hsk c = decodeEdges_ge_two hM hroot hk hsk d) : c.1 = d.1 := by
  apply Subtype.ext
  rw [← decode_intrinsic_junctions_ge_two hM hroot hr hk hsk c,
    ← decode_intrinsic_junctions_ge_two hM hroot hr hk hsk d, he]

include hr in
private theorem dirs_of_edges_ge_two {edges edges' : Finset (Finset V)}
    (C : MixedCycleWitness r markers edges) (D : MixedCycleWitness r markers edges')
    (he : edges = edges') (root : ↥markers)
    (h : C.markerStart root = D.markerStart root) :
    C.markerDirections root.val = D.markerDirections root.val := by
  subst edges'
  exact C.markerDirections_eq_of_root D hr root h

include hr in
theorem decode_eq_directions_ge_two {c d : CompleteHostCode r k markers root}
    (he : decodeEdges_ge_two hM hroot hk hsk c = decodeEdges_ge_two hM hroot hk hsk d) :
    c.2.1 = d.2.1 := by
  rw [← decode_markerDirections_ge_two hM hroot hr hk hsk c,
    ← decode_markerDirections_ge_two hM hroot hr hk hsk d]
  apply dirs_of_edges_ge_two hr _ _ he ⟨root, hroot⟩
  rw [decode_root_start_ge_two, decode_root_start_ge_two]

theorem order_eq_of_decodeOrder_eq_ge_two
    (J : ↥(ordinaryJunctionChoices markers k)) (dir : MarkerDirections markers root)
    (o o' : BlockEnumeration.RootedOrder k)
    (P P' : Allocation.Blocks (PrivatePool markers J.val) k (r - 2))
    (h : decodeOrder_ge_two hk hsk ⟨J, dir, o, P⟩ = decodeOrder_ge_two hk hsk ⟨J, dir, o', P'⟩) :
    o = o' := by
  apply (rootedOrderCycleEquiv k (by omega)).injective
  apply Subtype.ext
  apply Equiv.ext
  intro x
  have hh := Equiv.congr_fun h ((codeBlockLabels markers k hsk J).symm x)
  exact (codeBlockLabels markers k hsk J).symm.injective (by
    simpa only [decodeOrder_ge_two, permutationTransport_apply, Equiv.symm_symm,
      Equiv.apply_symm_apply] using hh)

include hr in
theorem decode_eq_remaining_ge_two
    (J : ↥(ordinaryJunctionChoices markers k)) (dir : MarkerDirections markers root)
    (o o' : BlockEnumeration.RootedOrder k)
    (P P' : Allocation.Blocks (PrivatePool markers J.val) k (r - 2))
    (he : decodeEdges_ge_two hM hroot hk hsk ⟨J, dir, o, P⟩ =
      decodeEdges_ge_two hM hroot hk hsk ⟨J, dir, o', P'⟩) : o = o' ∧ P = P' := by
  let c : CompleteHostCode r k markers root := ⟨J, dir, o, P⟩
  let d : CompleteHostCode r k markers root := ⟨J, dir, o', P'⟩
  let C := decodeWitness_ge_two hM hroot hr hk hsk c
  let D := decodeWitness_ge_two hM hroot hr hk hsk d
  have hroot' : C.markerStart ⟨root, hroot⟩ = D.markerStart ⟨root, hroot⟩ := by
    exact (decode_root_start_ge_two hM hroot hr hk hsk c).trans
      (decode_root_start_ge_two hM hroot hr hk hsk d).symm
  have hend (b : ↥markers ⊕ ↥J.val) :
      C.blockEnd (decodedBlockEquiv_ge_two hM hroot hr hk hsk c b) =
      D.blockEnd (decodedBlockEquiv_ge_two hM hroot hr hk hsk d b) := by
    rw [decoded_blockEnd_ge_two, decoded_blockEnd_ge_two]
  constructor
  · apply order_eq_of_decodeOrder_eq_ge_two hk hsk J dir o o' P P'
    apply Equiv.ext
    intro b
    have h := C.physical_next_junction D he hr ⟨root, hroot⟩ hroot'
      (decodedBlockEquiv_ge_two hM hroot hr hk hsk c b)
      (decodedBlockEquiv_ge_two hM hroot hr hk hsk d b) (hend b)
    rw [decoded_next_junction_ge_two, decoded_next_junction_ge_two] at h
    exact Sum.inl_injective ((codeJunction hM hroot dir J).injective h)
  · apply Subtype.ext
    funext i
    have h := C.physical_privateBlock D he hr ⟨root, hroot⟩ hroot'
      (decodedBlockEquiv_ge_two hM hroot hr hk hsk c ((codeBlockLabels markers k hsk J).symm i))
      (decodedBlockEquiv_ge_two hM hroot hr hk hsk d ((codeBlockLabels markers k hsk J).symm i))
      (hend _)
    rw [decoded_privateBlock_ge_two, decoded_privateBlock_ge_two] at h
    simpa only [c, d, Allocation.liftBlocks, Equiv.apply_symm_apply, Finset.map_inj] using h

include hr in
theorem decodeEdges_injective_ge_two : Function.Injective (decodeEdges_ge_two hM hroot hk hsk (r := r)) := by
  intro c d he
  have hJ := decode_eq_junction_choice_ge_two hM hroot hr hk hsk he
  have hd := decode_eq_directions_ge_two hM hroot hr hk hsk he
  rcases c with ⟨J, dir, o, P⟩
  rcases d with ⟨J', dir', o', P'⟩
  dsimp at hJ hd
  subst J'
  subst dir'
  obtain ⟨ho, hP⟩ := decode_eq_remaining_ge_two hM hroot hr hk hsk J dir o o' P P' he
  subst o'
  subst P'
  rfl

end LooseHamilton.CompleteHostCode
