module

public import HittingTimeLooseHamilton.OrientationUniqueness

public section

/-! Directed clone edges of an actual connected mixed cycle. The three tags mean
out-slot, in-slot, and the single uncoloured private slot respectively. -/
noncomputable section
open Finset
namespace LooseHamilton.MixedCycleWitness
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {r : ℕ} {markers edges : Finset (Finset V)}

/-- The clone edge of an ordinary edge in a directed cyclic presentation. -/
@[expose] def cloneEdge (C : MixedCycleWitness r markers edges) (e : ↥edges) :
    Finset (V × Fin 3) :=
  {(C.junction (C.slot.symm (.inr e)), 0),
    (C.junction (finRotate C.length (C.slot.symm (.inr e))), 1)} ∪
      (C.privateBlock e).image (fun v => (v, 2))

@[simp] theorem mem_cloneEdge (C : MixedCycleWitness r markers edges)
    (e : ↥edges) (v : V) (t : Fin 3) :
    (v,t) ∈ C.cloneEdge e ↔
      (v = C.junction (C.slot.symm (.inr e)) ∧ t = 0) ∨
      (v = C.junction (finRotate C.length (C.slot.symm (.inr e))) ∧ t = 1) ∨
      (v ∈ C.privateBlock e ∧ t = 2) := by
  simp [cloneEdge, Prod.ext_iff, and_assoc, eq_comm]

theorem cloneEdge_card (C : MixedCycleWitness r markers edges) (hr : 3 ≤ r)
    (e : ↥edges) : (C.cloneEdge e).card = r := by
  have hd : Disjoint
      ({(C.junction (C.slot.symm (.inr e)), 0),
        (C.junction (finRotate C.length (C.slot.symm (.inr e))), 1)} : Finset (V × Fin 3))
      ((C.privateBlock e).image (fun v => (v, (2 : Fin 3)))) := by
    apply disjoint_left.mpr
    intro x hx hy
    obtain ⟨w, hw, he⟩ := mem_image.mp hy
    have ht := congrArg Prod.snd he
    rcases mem_insert.mp hx with hx | hx
    · rw [hx] at ht
      exact (by decide : (2 : Fin 3) ≠ 0) ht
    · have hx := mem_singleton.mp hx
      rw [hx] at ht
      exact (by decide : (2 : Fin 3) ≠ 1) ht
  rw [cloneEdge, card_union_of_disjoint hd, card_image_of_injective]
  · simp only [card_pair (by simp :
      (C.junction (C.slot.symm (.inr e)), (0 : Fin 3)) ≠
      (C.junction (finRotate C.length (C.slot.symm (.inr e))), 1)), C.private_card]
    omega
  · intro x y h
    exact congrArg Prod.fst h

theorem cloneEdge_project (C : MixedCycleWitness r markers edges) (e : ↥edges) :
    (C.cloneEdge e).image Prod.fst = e.val := by
  have h := C.slot_edge (C.slot.symm (.inr e))
  rw [C.slot.apply_symm_apply] at h
  simp only at h
  simpa [cloneEdge, image_union, image_image, Function.comp_def] using h.symm

theorem cloneEdge_injective (C : MixedCycleWitness r markers edges) :
    Function.Injective C.cloneEdge := by
  intro e f h
  apply Subtype.ext
  simpa only [C.cloneEdge_project] using congrArg (fun a : Finset (V × Fin 3) => a.image Prod.fst) h

theorem cloneEdge_disjoint (C : MixedCycleWitness r markers edges) :
    Pairwise (fun e f => Disjoint (C.cloneEdge e) (C.cloneEdge f)) := by
  intro e f hef
  apply disjoint_left.mpr
  rintro ⟨v,t⟩ hv hw
  rw [mem_cloneEdge] at hv hw
  rcases hv with ⟨hv,ht⟩ | ⟨hv,ht⟩ | ⟨hv,ht⟩ <;>
    rcases hw with ⟨hw,hs⟩ | ⟨hw,hs⟩ | ⟨hw,hs⟩
  · exact hef (Sum.inr.inj (C.slot.symm.injective (C.junction_injective (hv.symm.trans hw))))
  · omega
  · omega
  · omega
  · exact hef (Sum.inr.inj (C.slot.symm.injective
      ((finRotate C.length).injective (C.junction_injective (hv.symm.trans hw)))))
  · omega
  · omega
  · omega
  · exact disjoint_left.mp (C.private_disjoint hef) hv hw

/-- This family samples only the lift of this connected cycle. -/
@[expose] def cloneMatching (C : MixedCycleWitness r markers edges) :
    Finset (Finset (V × Fin 3)) := univ.image C.cloneEdge

theorem cloneMatching_project (C : MixedCycleWitness r markers edges) :
    C.cloneMatching.image (fun e => e.image Prod.fst) = edges := by
  ext e
  simp only [cloneMatching, mem_image, mem_univ, true_and]
  constructor
  · rintro ⟨_, ⟨a, rfl⟩, h⟩
    rw [C.cloneEdge_project] at h
    exact h ▸ a.property
  · intro he
    exact ⟨C.cloneEdge ⟨e,he⟩, ⟨⟨e,he⟩, rfl⟩, C.cloneEdge_project _⟩

theorem cloneMatching_card (C : MixedCycleWitness r markers edges) :
    C.cloneMatching.card = edges.card := by
  rw [cloneMatching, card_image_of_injective _ C.cloneEdge_injective]
  simp

/-- Root orientation removes any dependence on the cyclic parametrisation. -/
theorem cloneEdge_eq_of_root (C D : MixedCycleWitness r markers edges) (hr : 3 ≤ r)
    (root : ↥markers) (hroot : C.markerStart root = D.markerStart root) (e : ↥edges) :
    C.cloneEdge e = D.cloneEdge e := by
  rw [cloneEdge, cloneEdge, C.slot_start_eq_of_root D hr root hroot (.inr e),
    C.slot_end_eq_of_root D hr root hroot (.inr e), C.privateBlock_eq D hr e]

theorem cloneMatching_eq_of_root (C D : MixedCycleWitness r markers edges) (hr : 3 ≤ r)
    (root : ↥markers) (hroot : C.markerStart root = D.markerStart root) :
    C.cloneMatching = D.cloneMatching := by
  unfold cloneMatching
  congr 1
  funext e
  exact C.cloneEdge_eq_of_root D hr root hroot e

end LooseHamilton.MixedCycleWitness
