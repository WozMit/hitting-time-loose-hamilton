module

public import HittingTimeLooseHamilton.Contraction
public import HittingTimeLooseHamilton.EnumerationCodes

public section

/-! Private allocations extracted from actual mixed-cycle witnesses. -/
noncomputable section
open Finset
namespace LooseHamilton.MixedCycleWitness
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {r : ℕ} {markers edges : Finset (Finset V)}

lemma ports_union_ordinaryJunctions (C : MixedCycleWitness r markers edges) :
    originalPorts markers ∪ C.ordinaryJunctionChoice.val = univ.image C.junction := by
  change markers.biUnion id ∪ (univ.image C.junction \ markers.biUnion id) = _
  exact union_sdiff_of_subset C.marked_vertices_subset_junctions

lemma mem_privatePool_iff (C : MixedCycleWitness r markers edges) (v : V) :
    v ∈ univ \ (originalPorts markers ∪ C.ordinaryJunctionChoice.val) ↔
      v ∉ univ.image C.junction := by
  rw [C.ports_union_ordinaryJunctions]
  simp

lemma private_mem_pool (C : MixedCycleWitness r markers edges) (e : ↥edges)
    {v : V} (hv : v ∈ C.privateBlock e) :
    v ∈ univ \ (originalPorts markers ∪ C.ordinaryJunctionChoice.val) := by
  apply (C.mem_privatePool_iff v).mpr
  exact fun hj => disjoint_left.mp (C.junction_private_disjoint e) hj hv

lemma privatePool_unique (C : MixedCycleWitness r markers edges)
    (v : PrivatePool markers C.ordinaryJunctionChoice.val) :
    ∃! e : ↥edges, v.val ∈ C.privateBlock e := by
  have hn := (C.mem_privatePool_iff v.val).mp v.property
  have hv : v.val ∈ univ.image C.junction ∪ univ.biUnion C.privateBlock := by
    rw [← C.cover]
    exact mem_univ _
  obtain ⟨e, _, he⟩ := mem_biUnion.mp ((mem_union.mp hv).resolve_left hn)
  refine ⟨e, he, ?_⟩
  intro f hf
  by_contra hfe
  exact disjoint_left.mp (C.private_disjoint hfe) hf he

/-- Restrict a private block to the intrinsic pool of non-junction vertices. -/
@[expose] def privatePoolBlock (C : MixedCycleWitness r markers edges) (e : ↥edges) :
    Finset (PrivatePool markers C.ordinaryJunctionChoice.val) :=
  univ.filter (fun v => v.val ∈ C.privateBlock e)

@[simp] theorem mem_privatePoolBlock (C : MixedCycleWitness r markers edges) (e : ↥edges)
    (v : PrivatePool markers C.ordinaryJunctionChoice.val) :
    v ∈ C.privatePoolBlock e ↔ v.val ∈ C.privateBlock e := by simp [privatePoolBlock]

@[expose] def privatePoolBlockEquiv (C : MixedCycleWitness r markers edges) (e : ↥edges) :
    ↥(C.privatePoolBlock e) ≃ ↥(C.privateBlock e) where
  toFun v := ⟨v.val.val, (C.mem_privatePoolBlock e v.val).mp v.property⟩
  invFun v := ⟨⟨v.val, C.private_mem_pool e v.property⟩,
    (C.mem_privatePoolBlock e _).mpr v.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

@[simp] theorem privatePoolBlock_card (C : MixedCycleWitness r markers edges) (e : ↥edges) :
    (C.privatePoolBlock e).card = r - 2 := by
  rw [← Fintype.card_coe, Fintype.card_congr (C.privatePoolBlockEquiv e),
    Fintype.card_coe, C.private_card]

/-- The private blocks attached to each labelled contracted block. -/
@[expose] def privateAllocation (C : MixedCycleWitness r markers edges) {k : ℕ}
    (labels : C.ContractedBlock ≃ Fin k) :
    Allocation.Blocks (PrivatePool markers C.ordinaryJunctionChoice.val) k (r-2) :=
  ⟨fun i => C.privatePoolBlock (C.blockEdgeEquiv (labels.symm i)), by
    constructor
    · intro i; exact C.privatePoolBlock_card _
    · intro v
      obtain ⟨e, he, hu⟩ := C.privatePool_unique v
      refine ⟨labels (C.blockEdgeEquiv.symm e), ?_, ?_⟩
      · simpa using he
      · intro i hi
        have h : C.blockEdgeEquiv (labels.symm i) = e :=
          hu _ ((C.mem_privatePoolBlock _ _).mp hi)
        apply labels.symm.injective
        apply C.blockEdgeEquiv.injective
        simpa using h⟩

@[simp] theorem mem_privateAllocation (C : MixedCycleWitness r markers edges) {k : ℕ}
    (labels : C.ContractedBlock ≃ Fin k) (i : Fin k)
    (v : PrivatePool markers C.ordinaryJunctionChoice.val) :
    v ∈ (C.privateAllocation labels).val i ↔
      v.val ∈ C.privateBlock (C.blockEdgeEquiv (labels.symm i)) :=
  C.mem_privatePoolBlock _ _

/-- Canonical finite labels for the contracted blocks of a given witness. -/
@[expose] def canonicalBlockLabels (C : MixedCycleWitness r markers edges) :
    C.ContractedBlock ≃ Fin edges.card :=
  Fintype.equivOfCardEq (by rw [C.contractedBlock_card, Fintype.card_fin])

end LooseHamilton.MixedCycleWitness
