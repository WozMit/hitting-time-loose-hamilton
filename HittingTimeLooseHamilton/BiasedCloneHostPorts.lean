module

public import HittingTimeLooseHamilton.BiasedCloneHostAverage
public import HittingTimeLooseHamilton.BiasedCloneUniverse

public section

noncomputable section
open Finset
namespace LooseHamilton.MixedCycleWitness
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {r : ℕ} {markers edges : Finset (Finset V)}

/-- The two slots occupied by each directed marker. -/
@[expose] def occupiedCloneSlots (C : MixedCycleWitness r markers edges) : Finset (V × Fin 3) :=
  C.markerStarts.image (fun v => (v,0)) ∪ C.markerEnds.image (fun v => (v,1))

theorem occupiedCloneSlots_card_le (C : MixedCycleWitness r markers edges) :
    C.occupiedCloneSlots.card ≤ 2*markers.card := by
  have h₁ : C.markerStarts.card ≤ markers.card := by
    simpa [markerStarts] using (card_image_le :
      (univ.image (fun e : ↥markers => C.junction (C.slot.symm (.inl e)))).card ≤ univ.card)
  have h₂ : C.markerEnds.card ≤ markers.card := by
    simpa [markerEnds] using (card_image_le :
      (univ.image (fun e : ↥markers => C.junction (finRotate C.length (C.slot.symm (.inl e))))).card ≤ univ.card)
  exact (card_union_le _ _).trans ((Nat.add_le_add card_image_le card_image_le).trans
    (by omega : C.markerStarts.card+C.markerEnds.card ≤ 2*markers.card))

theorem cloneVertices_eq_full_sdiff (C : MixedCycleWitness r markers edges) :
    C.cloneVertices = fullCloneSlots (univ.image C.junction) \ C.occupiedCloneSlots := by
  ext ⟨v,t⟩
  rw [C.mem_cloneVertices]
  simp only [mem_sdiff, mem_fullCloneSlots, occupiedCloneSlots, mem_union, mem_image]
  simp only [Prod.mk.injEq, exists_eq_right, and_assoc]
  by_cases ht₀ : t=0
  · subst t
    simp
  by_cases ht₁ : t=1
  · subst t
    simp
  have ht₂ : t=2 := by omega
  subst t
  simp

theorem cloneHost_cycle_port_error (C : MixedCycleWitness r markers edges)
    (G : SimpleHypergraph V) (L : ℕ) (hG : ∀e∈G,e.card=r)
    (hdeg : ∀v, vertexDegree G v ≤ L) :
    (cloneHost G C.cloneVertices).card ≤ 2*partitionCount G (univ.image C.junction) ∧
    2*partitionCount G (univ.image C.junction) ≤
      (cloneHost G C.cloneVertices).card + (2*markers.card)*(r*r*L) := by
  rw [C.cloneVertices_eq_full_sdiff]
  have h := cloneHost_port_error G (univ.image C.junction) C.occupiedCloneSlots r L hG
    (fun x hx => hdeg x.1)
  refine ⟨h.1, h.2.trans ?_⟩
  exact Nat.add_le_add_left (Nat.mul_le_mul_right _ C.occupiedCloneSlots_card_le) _
end LooseHamilton.MixedCycleWitness
