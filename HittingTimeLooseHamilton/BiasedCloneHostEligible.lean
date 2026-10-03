module

public import HittingTimeLooseHamilton.BiasedCloneHostPorts
public import HittingTimeLooseHamilton.IntrinsicRoles

public section

noncomputable section
open Finset
namespace LooseHamilton.MixedCycleWitness
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {r : ℕ} {markers edges : Finset (Finset V)}

theorem markerStarts_subset_ports (C : MixedCycleWitness r markers edges) :
    C.markerStarts ⊆ originalPorts markers := by
  intro v hv
  obtain ⟨m,_,rfl⟩ := mem_image.mp hv
  apply mem_biUnion.mpr
  refine ⟨m.val,m.property,?_⟩
  have he := C.slot_edge (C.slot.symm (.inl m))
  rw [C.slot.apply_symm_apply] at he
  dsimp only at he
  rw [he]
  simp

theorem markerEnds_subset_ports (C : MixedCycleWitness r markers edges) :
    C.markerEnds ⊆ originalPorts markers := by
  intro v hv
  obtain ⟨m,_,rfl⟩ := mem_image.mp hv
  apply mem_biUnion.mpr
  refine ⟨m.val,m.property,?_⟩
  have he := C.slot_edge (C.slot.symm (.inl m))
  rw [C.slot.apply_symm_apply] at he
  dsimp only at he
  rw [he]
  simp

theorem mem_cloneVertices_away_ports (C : MixedCycleWitness r markers edges)
    (v : V) (t : Fin 3) (hv : v∉originalPorts markers) :
    (v,t)∈C.cloneVertices ↔ (v,t)∈fullCloneSlots (univ.image C.junction) := by
  have hs : v∉C.markerStarts := fun h => hv (C.markerStarts_subset_ports h)
  have he : v∉C.markerEnds := fun h => hv (C.markerEnds_subset_ports h)
  rw [C.mem_cloneVertices, mem_fullCloneSlots]
  simp only [hs,he,not_false_eq_true,true_and]
  tauto

theorem eligible_directedCloneEdge_subset_iff (C : MixedCycleWitness r markers edges)
    (e : Finset V) {a b : V} (ha : a∈e) (hb : b∈e)
    (he : Disjoint e (originalPorts markers)) :
    directedCloneEdge e a b ⊆ C.cloneVertices ↔ e∩univ.image C.junction={a,b} := by
  rw [← directedCloneEdge_subset_full e (univ.image C.junction) ha hb]
  have hmem : ∀ x∈directedCloneEdge e a b,
      x∈C.cloneVertices ↔ x∈fullCloneSlots (univ.image C.junction) := by
    intro x hx
    have hv : x.1∈e := (directedCloneEdge_project e ha hb) ▸ mem_image_of_mem Prod.fst hx
    exact C.mem_cloneVertices_away_ports x.1 x.2 (disjoint_left.mp he hv)
  constructor <;> intro h x hx
  · exact (hmem x hx).mp (h hx)
  · exact (hmem x hx).mpr (h hx)

theorem eligible_directedCloneEdge_ordinary_iff (C : MixedCycleWitness r markers edges)
    (hr : 3≤r) (e : Finset V) {a b : V} (ha : a∈e) (hb : b∈e)
    (he : Disjoint e (originalPorts markers)) :
    directedCloneEdge e a b ⊆ C.cloneVertices ↔ e∩ordinaryJunctions markers edges={a,b} := by
  rw [C.eligible_directedCloneEdge_subset_iff e ha hb he]
  have hh : e∩ordinaryJunctions markers edges=e∩univ.image C.junction := by
    rw [ordinaryJunctions, C.cycleJunctions_eq hr]
    ext v
    simp only [mem_inter, mem_sdiff]
    constructor
    · exact fun h => ⟨h.1,h.2.1⟩
    · exact fun h => ⟨h.1,h.2,disjoint_left.mp he h.1⟩
  rw [hh]
end LooseHamilton.MixedCycleWitness
