module

public import HittingTimeLooseHamilton.BlockCycle
public import HittingTimeLooseHamilton.PairOrientations
public import HittingTimeLooseHamilton.AllocationLift
public import HittingTimeLooseHamilton.EnumerationCodes

public section
noncomputable section
open Finset
namespace LooseHamilton
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {r k : ℕ} {markers : Finset (Finset V)} {root : Finset V}
/-- Actual junction embedding for the oriented block labels. -/
@[expose] def codeJunction (hM : IsPairMatching markers) (hroot : root ∈ markers)
    (dir : MarkerDirections markers root) (J : ↥(ordinaryJunctionChoices markers k)) :
    BlockJunctions markers ↥J.val ↪ V :=
  (expandedJunctionEquiv hM root hroot dir J.val
    ((mem_ordinaryJunctionChoices _ _ _).mp J.property).1).toEmbedding.trans
      ⟨Subtype.val, Subtype.val_injective⟩

theorem codeJunction_image (hM : IsPairMatching markers) (hroot : root ∈ markers)
    (dir : MarkerDirections markers root) (J : ↥(ordinaryJunctionChoices markers k)) :
    univ.image (codeJunction hM hroot dir J) = originalPorts markers ∪ J.val := by
  let e := expandedJunctionEquiv hM root hroot dir J.val
    ((mem_ordinaryJunctionChoices _ _ _).mp J.property).1
  ext v
  constructor
  · rintro hv
    obtain ⟨a, _, rfl⟩ := mem_image.mp hv
    exact (e a).property
  · intro hv
    refine mem_image.mpr ⟨e.symm ⟨v, hv⟩, mem_univ _, ?_⟩
    exact congrArg Subtype.val (e.apply_symm_apply ⟨v, hv⟩)

/-- The forward construction from a cyclic order of the contracted blocks and private allocation. -/
@[expose] def decodeBlockData (hM : IsPairMatching markers) (hroot : root ∈ markers)
    (J : ↥(ordinaryJunctionChoices markers k))
    (dir : MarkerDirections markers root)
    (b : (↥markers ⊕ ↥J.val) ≃ Fin k)
    (σ : Equiv.Perm (↥markers ⊕ ↥J.val)) (hσ : σ.IsCycleOn Set.univ)
    (hcard : 3 ≤ Fintype.card (BlockJunctions markers ↥J.val))
    (P : Allocation.Blocks (PrivatePool markers J.val) k (r - 2)) :
    PermutationCycleData r markers (BlockJunctions markers ↥J.val) (↥markers ⊕ ↥J.val) := by
  let j := codeJunction hM hroot dir J
  let u : PrivatePool markers J.val ↪ V := ⟨Subtype.val, Subtype.val_injective⟩
  let Q := Allocation.liftBlocks P u b
  have hj : univ.image j = originalPorts markers ∪ J.val := codeJunction_image hM hroot dir J
  have hu : univ.map u = univ \ (originalPorts markers ∪ J.val) := by
    ext v
    simp only [mem_map, mem_univ, true_and]
    constructor
    · rintro ⟨a, rfl⟩; exact a.property
    · intro hv; exact ⟨⟨v, hv⟩, rfl⟩
  refine blockCycleData σ hσ hcard (.inl ⟨root, hroot⟩) j Q
    (Allocation.liftBlocks_card P u b) (Allocation.liftBlocks_disjoint P u b) ?_ ?_ hM.2 ?_
  · intro a
    rw [hj]
    apply disjoint_sdiff_self_right.mono_right
    rw [← hu]
    exact Allocation.liftBlocks_subset P u b a
  · rw [hj, Allocation.liftBlocks_union P u b, hu]
    exact (union_sdiff_of_subset (subset_univ _)).symm
  · intro m
    exact marker_eq_endpoints hM root hroot dir m
end LooseHamilton
