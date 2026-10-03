module

public import HittingTimeLooseHamilton.BiasedCloneHostProperties

public section

noncomputable section
open Finset
namespace LooseHamilton.MixedCycleWitness
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {r : ℕ} {markers edges : Finset (Finset V)}

theorem cloneEdge_directed_eq (C : MixedCycleWitness r markers edges) (e : ↥edges) :
    C.cloneEdge e = directedCloneEdge e.val
      (C.junction (C.slot.symm (.inr e)))
      (C.junction (finRotate C.length (C.slot.symm (.inr e)))) := by
  have he := C.slot_edge (C.slot.symm (.inr e))
  rw [C.slot.apply_symm_apply] at he
  dsimp only at he
  have hd : Disjoint
      ({C.junction (C.slot.symm (.inr e)), C.junction (finRotate C.length (C.slot.symm (.inr e)))} : Finset V)
      (C.privateBlock e) := by
    apply (C.junction_private_disjoint e).mono_left
    intro v hv
    rcases mem_insert.mp hv with rfl | hv
    · exact mem_image_of_mem _ (mem_univ _)
    · rw [mem_singleton] at hv
      subst v
      exact mem_image_of_mem _ (mem_univ _)
  have hp : e.val \ {C.junction (C.slot.symm (.inr e)),
      C.junction (finRotate C.length (C.slot.symm (.inr e)))} = C.privateBlock e := by
    rw [he, union_sdiff_left]
    exact sdiff_eq_self_iff_disjoint.mpr hd.symm
  simp only [cloneEdge, directedCloneEdge, hp]

theorem cloneEdge_mem_directedCloneEdges (C : MixedCycleWitness r markers edges)
    (e : ↥edges) : C.cloneEdge e ∈ directedCloneEdges e.val := by
  let a := C.junction (C.slot.symm (.inr e))
  let b := C.junction (finRotate C.length (C.slot.symm (.inr e)))
  have he := C.slot_edge (C.slot.symm (.inr e))
  rw [C.slot.apply_symm_apply] at he
  dsimp only at he
  have ha : a∈e.val := by rw [he]; simp [a]
  have hb : b∈e.val := by rw [he]; simp [b]
  rw [C.cloneEdge_directed_eq]
  exact mem_image.mpr ⟨(a,b), mem_filter.mpr ⟨mem_product.mpr ⟨ha,hb⟩,
    C.junction_next_ne _⟩, rfl⟩

theorem cloneMatching_subset_host (C : MixedCycleWitness r markers edges)
    (G : SimpleHypergraph V) (U : Finset (V × Fin 3))
    (hG : edges⊆G) (hU : C.cloneVertices⊆U) :
    C.cloneMatching ⊆ cloneHost G U := by
  intro B hB
  obtain ⟨e,_,rfl⟩ := mem_image.mp hB
  apply mem_filter.mpr
  constructor
  · exact mem_biUnion.mpr ⟨e.val,hG e.property,C.cloneEdge_mem_directedCloneEdges e⟩
  · intro x hx
    exact hU (mem_biUnion.mpr ⟨e,mem_univ _,hx⟩)
end LooseHamilton.MixedCycleWitness
