module

public import HittingTimeLooseHamilton.IntrinsicRoles

public section

/-! # Partitioning actual cycle incidences by their two junctions

The endpoint pair is recovered from the whole edge set. Consequently each
unoriented cycle containing a fixed edge belongs to exactly one role class.
-/
noncomputable section
open Finset
open scoped BigOperators
namespace LooseHamilton
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The two junctions of an ordinary edge, determined by the counted edge set. -/
@[expose] def edgeEndpointPair (markers edges : Finset (Finset V)) (e : Finset V) : Finset V :=
  e ∩ cycleJunctions markers edges

namespace MixedCycleWitness
variable {r : ℕ} {markers edges : Finset (Finset V)}

theorem edgeEndpointPair_eq (C : MixedCycleWitness r markers edges) (hr : 3 ≤ r)
    (e : ↥edges) : edgeEndpointPair markers edges e.val =
      {C.junction (C.slot.symm (.inr e)),
        C.junction (finRotate C.length (C.slot.symm (.inr e)))} := by
  rw [edgeEndpointPair, C.cycleJunctions_eq hr]
  simpa only [slotSet, C.slot.apply_symm_apply, Sum.elim_inr] using
    C.slotSet_inter_junctions (C.slot.symm (.inr e))

theorem edgeEndpointPair_card (C : MixedCycleWitness r markers edges) (hr : 3 ≤ r)
    (e : ↥edges) : (edgeEndpointPair markers edges e.val).card = 2 := by
  rw [C.edgeEndpointPair_eq hr e, card_pair (C.junction_next_ne _)]

theorem private_eq_sdiff_endpointPair (C : MixedCycleWitness r markers edges) (hr : 3 ≤ r)
    (e : ↥edges) : C.privateBlock e = e.val \ edgeEndpointPair markers edges e.val := by
  rw [edgeEndpointPair, sdiff_inter_self_left, C.cycleJunctions_eq hr]
  exact C.private_eq_sdiff_junctions e
end MixedCycleWitness

/-- Cycles containing e whose uniquely determined endpoint pair is q. -/
@[expose] def edgeRoleFamily (r : ℕ) (markers host : Finset (Finset V)) (e q : Finset V) :
    Finset (Finset (Finset V)) :=
  (unrestrictedCycleFamily r markers host).filter
    (fun E => e ∈ E ∧ edgeEndpointPair markers E e = q)

@[simp] theorem mem_edgeRoleFamily (r : ℕ) (markers host : Finset (Finset V))
    (e q : Finset V) (E : Finset (Finset V)) (hr : 3 ≤ r) :
    E ∈ edgeRoleFamily r markers host e q ↔
      IsMixedCycle r markers E ∧ E ⊆ host ∧ e ∈ E ∧ edgeEndpointPair markers E e = q := by
  simp only [edgeRoleFamily, mem_filter, mem_unrestrictedCycleFamily _ _ _ _ hr]
  tauto

/-- Every incidence contributes once to the sum over unordered pairs in e. -/
theorem edge_incidence_partition (r : ℕ) (markers host : Finset (Finset V))
    (e : Finset V) (hr : 3 ≤ r) :
    FiniteFamily.incidenceCount (unrestrictedCycleFamily r markers host) e =
      ∑ q ∈ e.powersetCard 2, (edgeRoleFamily r markers host e q).card := by
  let F := (unrestrictedCycleFamily r markers host).filter (fun E => e ∈ E)
  have hmap : ∀ E ∈ F, edgeEndpointPair markers E e ∈ e.powersetCard 2 := by
    intro E hE
    obtain ⟨hE, he⟩ := mem_filter.mp hE
    have hC := ((mem_unrestrictedCycleFamily _ _ _ _ hr).mp hE).1
    obtain ⟨C⟩ := hC
    exact mem_powersetCard.mpr ⟨inter_subset_left, C.edgeEndpointPair_card hr ⟨e, he⟩⟩
  have h := card_eq_sum_card_fiberwise hmap
  change F.card = _
  rw [h]
  apply sum_congr rfl
  intro q hq
  congr 1
  ext E
  simp only [F, mem_filter, edgeRoleFamily]
  tauto

end LooseHamilton
