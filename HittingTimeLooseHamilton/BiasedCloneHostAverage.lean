module

public import HittingTimeLooseHamilton.BiasedCloneHostCount

public section

noncomputable section
open Finset
namespace LooseHamilton
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem fullCloneHost_card (G : SimpleHypergraph V) (A : Finset V) :
    (cloneHost G (fullCloneSlots A)).card = 2 * partitionCount G A := by
  classical
  unfold cloneHost
  rw [filter_biUnion, card_biUnion]
  · simp_rw [compatibleCloneEdges_card]
    have h : (∑ e∈G, if (e∩A).card=2 then 2 else 0) =
        ∑ e∈G, (if (e∩A).card=2 then 1 else 0) * 2 := by
      apply sum_congr rfl
      intro e he
      split <;> simp
    rw [h, ← sum_mul, sum_boole]
    simp [partitionCount, Nat.mul_comm]
  · intro e he f hf hef
    exact (directedCloneEdges_disjoint hef).mono (filter_subset _ _) (filter_subset _ _)

theorem cloneHost_mono_slots (G : SimpleHypergraph V) {U W : Finset (V × Fin 3)}
    (hUW : U⊆W) : cloneHost G U ⊆ cloneHost G W := by
  intro B hB
  obtain ⟨hB,hU⟩ := mem_filter.mp hB
  exact mem_filter.mpr ⟨hB,hU.trans hUW⟩

/-- Removing marker-occupied slots loses at most their total incident degree. -/
theorem cloneHost_slot_deletion_bound (G : SimpleHypergraph V)
    (U D : Finset (V × Fin 3)) (L : ℕ)
    (hdeg : ∀ x∈D, vertexDegree (cloneHost G U) x ≤ L) :
    (cloneHost G U).card ≤ (cloneHost G (U\D)).card + D.card*L := by
  let H := cloneHost G U
  let H' := cloneHost G (U\D)
  have hsub : H' ⊆ H := cloneHost_mono_slots G sdiff_subset
  have hcover : H\H' ⊆ D.biUnion (fun x => H.filter (fun B => x∈B)) := by
    intro B hB
    obtain ⟨hB,hn⟩ := mem_sdiff.mp hB
    have hU : B⊆U := (mem_filter.mp hB).2
    have hnot : ¬ B⊆U\D := by
      intro hh
      exact hn (mem_filter.mpr ⟨(mem_filter.mp hB).1,hh⟩)
    obtain ⟨x,hx,hxD⟩ := not_subset.mp hnot
    have hd : x∈D := by simpa [hU hx] using hxD
    exact mem_biUnion.mpr ⟨x,hd,mem_filter.mpr ⟨hB,hx⟩⟩
  have hc : (H\H').card ≤ D.card*L := (card_le_card hcover).trans
    (card_biUnion_le_card_mul D (fun x => H.filter (fun B => x∈B)) L hdeg)
  have hc' := card_sdiff_add_card_eq_card hsub
  change H.card ≤ H'.card + D.card*L
  omega

theorem cloneHost_port_error (G : SimpleHypergraph V) (A : Finset V)
    (D : Finset (V × Fin 3)) (r L : ℕ)
    (hG : ∀ e∈G, e.card=r) (hdeg : ∀ x∈D, vertexDegree G x.1 ≤ L) :
    (cloneHost G (fullCloneSlots A\D)).card ≤ 2*partitionCount G A ∧
    2*partitionCount G A ≤ (cloneHost G (fullCloneSlots A\D)).card + D.card*(r*r*L) := by
  constructor
  · rw [← fullCloneHost_card]
    exact card_le_card (cloneHost_mono_slots G sdiff_subset)
  · rw [← fullCloneHost_card]
    apply cloneHost_slot_deletion_bound
    intro x hx
    exact (cloneHost_degree_le G _ r hG x).trans (Nat.mul_le_mul_left _ (hdeg x hx))
end LooseHamilton
