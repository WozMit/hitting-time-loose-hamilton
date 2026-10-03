module

public import HittingTimeLooseHamilton.ActiveCycleRoles

public section

noncomputable section
open Finset
namespace LooseHamilton.MixedCycleOnWitness
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {r : ℕ} {S : Finset V} {M E : Finset (Finset V)}

/-- Every vertex meets at most two ordinary edges in an actual mixed cycle. -/
theorem incident_card_le_two (C : MixedCycleOnWitness r S M E) (v : V) :
    (E.filter (fun e => v ∈ e)).card ≤ 2 := by
  classical
  by_cases hj : v ∈ univ.image C.junction
  · obtain ⟨j, _, rfl⟩ := mem_image.mp hj
    apply le_trans (b := ({C.slotSet j, C.slotSet ((finRotate C.length).symm j)} : Finset (Finset V)).card)
      (card_le_card ?_) (by
        have h := card_pair_eq_one_or_two (a := C.slotSet j) (b := C.slotSet ((finRotate C.length).symm j))
        omega)
    intro e he
    obtain ⟨he, hv⟩ := mem_filter.mp he
    obtain ⟨i, rfl⟩ := C.slotSet_surjective (mem_union_right M he)
    have hi : C.junction j ∈ C.slotSet i ∩ univ.image C.junction :=
      mem_inter.mpr ⟨hv, mem_image_of_mem _ (mem_univ _)⟩
    rw [C.slotSet_inter_junctions] at hi
    simp only [mem_insert, mem_singleton] at hi ⊢
    rcases hi with hi | hi
    · left
      exact congrArg C.slotSet (C.junction_injective hi).symm
    · right
      have hji := C.junction_injective hi
      have hij : i = (finRotate C.length).symm j := by
        rw [hji, Equiv.symm_apply_apply]
      exact congrArg C.slotSet hij
  · by_cases hn : (E.filter (fun e => v ∈ e)).Nonempty
    · obtain ⟨e, he⟩ := hn
      obtain ⟨he, hv⟩ := mem_filter.mp he
      have hp : v ∈ C.privateBlock ⟨e,he⟩ := by
        rw [C.private_eq_sdiff_junctions]
        exact mem_sdiff.mpr ⟨hv,hj⟩
      have hs : E.filter (fun e => v ∈ e) ⊆ {e} := by
        intro f hf
        obtain ⟨hf,hvf⟩ := mem_filter.mp hf
        exact mem_singleton.mpr (C.private_unique_edge ⟨e,he⟩ hp (mem_union_right M hf) hvf)
      have hc := card_le_card hs
      simpa only [card_singleton] using hc.trans (by decide : 1 ≤ 2)
    · rw [not_nonempty_iff_eq_empty.mp hn, card_empty]
      omega
end LooseHamilton.MixedCycleOnWitness
