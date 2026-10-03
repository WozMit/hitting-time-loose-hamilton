module

public import HittingTimeLooseHamilton.DecodeBlockRecovery
public import HittingTimeLooseHamilton.WitnessPhysicalUniqueness
public import HittingTimeLooseHamilton.IntrinsicRoles
public import HittingTimeLooseHamilton.OrientationUniqueness

public section
noncomputable section
open Finset
namespace LooseHamilton.CompleteHostCode
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {r k : ℕ} {markers : Finset (Finset V)} {root : Finset V}
variable (hM : IsPairMatching markers) (hroot : root ∈ markers)
  (hr : 3 ≤ r) (hk : 3 ≤ k) (hsk : markers.card ≤ k)

include hr in
theorem decode_intrinsic_junctions (c : CompleteHostCode r k markers root) :
    ordinaryJunctions markers (decodeEdges hM hroot hk hsk c) = c.1.val := by
  rw [ordinaryJunctions, (decodeWitness hM hroot hr hk hsk c).cycleJunctions_eq hr]
  exact decode_ordinaryJunctions hM hroot hr hk hsk c

include hr in
theorem decode_eq_junction_choice {c d : CompleteHostCode r k markers root}
    (he : decodeEdges hM hroot hk hsk c = decodeEdges hM hroot hk hsk d) : c.1 = d.1 := by
  apply Subtype.ext
  rw [← decode_intrinsic_junctions hM hroot hr hk hsk c,
    ← decode_intrinsic_junctions hM hroot hr hk hsk d, he]

include hr in
private theorem dirs_of_edges {edges edges' : Finset (Finset V)}
    (C : MixedCycleWitness r markers edges) (D : MixedCycleWitness r markers edges')
    (he : edges = edges') (root : ↥markers)
    (h : C.markerStart root = D.markerStart root) :
    C.markerDirections root.val = D.markerDirections root.val := by
  subst edges'
  exact C.markerDirections_eq_of_root D hr root h

include hr in
theorem decode_eq_directions {c d : CompleteHostCode r k markers root}
    (he : decodeEdges hM hroot hk hsk c = decodeEdges hM hroot hk hsk d) :
    c.2.1 = d.2.1 := by
  rw [← decode_markerDirections hM hroot hr hk hsk c,
    ← decode_markerDirections hM hroot hr hk hsk d]
  apply dirs_of_edges hr _ _ he ⟨root, hroot⟩
  rw [decode_root_start, decode_root_start]

theorem order_eq_of_decodeOrder_eq
    (J : ↥(ordinaryJunctionChoices markers k)) (dir : MarkerDirections markers root)
    (o o' : BlockEnumeration.RootedOrder k)
    (P P' : Allocation.Blocks (PrivatePool markers J.val) k (r - 2))
    (h : decodeOrder hk hsk ⟨J, dir, o, P⟩ = decodeOrder hk hsk ⟨J, dir, o', P'⟩) :
    o = o' := by
  apply (rootedOrderCycleEquiv k (by omega)).injective
  apply Subtype.ext
  apply Equiv.ext
  intro x
  have hh := Equiv.congr_fun h ((codeBlockLabels markers k hsk J).symm x)
  exact (codeBlockLabels markers k hsk J).symm.injective (by
    simpa only [decodeOrder, permutationTransport_apply, Equiv.symm_symm,
      Equiv.apply_symm_apply] using hh)

include hr in
theorem decode_eq_remaining
    (J : ↥(ordinaryJunctionChoices markers k)) (dir : MarkerDirections markers root)
    (o o' : BlockEnumeration.RootedOrder k)
    (P P' : Allocation.Blocks (PrivatePool markers J.val) k (r - 2))
    (he : decodeEdges hM hroot hk hsk ⟨J, dir, o, P⟩ =
      decodeEdges hM hroot hk hsk ⟨J, dir, o', P'⟩) : o = o' ∧ P = P' := by
  let c : CompleteHostCode r k markers root := ⟨J, dir, o, P⟩
  let d : CompleteHostCode r k markers root := ⟨J, dir, o', P'⟩
  let C := decodeWitness hM hroot hr hk hsk c
  let D := decodeWitness hM hroot hr hk hsk d
  have hroot' : C.markerStart ⟨root, hroot⟩ = D.markerStart ⟨root, hroot⟩ := by
    exact (decode_root_start hM hroot hr hk hsk c).trans
      (decode_root_start hM hroot hr hk hsk d).symm
  have hend (b : ↥markers ⊕ ↥J.val) :
      C.blockEnd (decodedBlockEquiv hM hroot hr hk hsk c b) =
      D.blockEnd (decodedBlockEquiv hM hroot hr hk hsk d b) := by
    rw [decoded_blockEnd, decoded_blockEnd]
  constructor
  · apply order_eq_of_decodeOrder_eq hk hsk J dir o o' P P'
    apply Equiv.ext
    intro b
    have h := C.physical_next_junction D he hr ⟨root, hroot⟩ hroot'
      (decodedBlockEquiv hM hroot hr hk hsk c b)
      (decodedBlockEquiv hM hroot hr hk hsk d b) (hend b)
    rw [decoded_next_junction, decoded_next_junction] at h
    exact Sum.inl_injective ((codeJunction hM hroot dir J).injective h)
  · apply Subtype.ext
    funext i
    have h := C.physical_privateBlock D he hr ⟨root, hroot⟩ hroot'
      (decodedBlockEquiv hM hroot hr hk hsk c ((codeBlockLabels markers k hsk J).symm i))
      (decodedBlockEquiv hM hroot hr hk hsk d ((codeBlockLabels markers k hsk J).symm i))
      (hend _)
    rw [decoded_privateBlock, decoded_privateBlock] at h
    simpa only [c, d, Allocation.liftBlocks, Equiv.apply_symm_apply, Finset.map_inj] using h

include hr in
theorem decodeEdges_injective : Function.Injective (decodeEdges hM hroot hk hsk (r := r)) := by
  intro c d he
  have hJ := decode_eq_junction_choice hM hroot hr hk hsk he
  have hd := decode_eq_directions hM hroot hr hk hsk he
  rcases c with ⟨J, dir, o, P⟩
  rcases d with ⟨J', dir', o', P'⟩
  dsimp at hJ hd
  subst J'
  subst dir'
  obtain ⟨ho, hP⟩ := decode_eq_remaining hM hroot hr hk hsk J dir o o' P P' he
  subst o'
  subst P'
  rfl

end LooseHamilton.CompleteHostCode
