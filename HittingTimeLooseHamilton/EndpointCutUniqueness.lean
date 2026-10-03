module

public import HittingTimeLooseHamilton.ActiveCycleRoles

public section

/-! # A marked port determines its unique ordinary incident edge -/
namespace LooseHamilton
namespace MixedCycleOnWitness
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {r : ℕ} {S : Finset V} {markers edges : Finset (Finset V)}

theorem ordinary_incident_marked_unique (C : MixedCycleOnWitness r S markers edges)
    (m : ↥markers) (e f : ↥edges) {v : V}
    (hvm : v ∈ m.val) (hve : v ∈ e.val) (hvf : v ∈ f.val) : e = f := by
  let i := C.slot.symm (.inl m)
  let j := C.slot.symm (.inr e)
  let k := C.slot.symm (.inr f)
  have hi : C.slot i = .inl m := C.slot.apply_symm_apply _
  have hj : C.slot j = .inr e := C.slot.apply_symm_apply _
  have hk : C.slot k = .inr f := C.slot.apply_symm_apply _
  have hm := C.slot_edge i
  rw [hi] at hm
  simp only at hm
  have hvJ : v ∈ univ.image C.junction := by
    rw [hm] at hvm
    rcases mem_insert.mp hvm with h | h
    · rw [h]; exact mem_image_of_mem _ (mem_univ _)
    · rw [mem_singleton.mp h]; exact mem_image_of_mem _ (mem_univ _)
  have he := C.slot_edge j
  rw [hj] at he
  simp only at he
  have hf := C.slot_edge k
  rw [hk] at hf
  simp only at hf
  have hve' : v ∈ ({C.junction j, C.junction (finRotate C.length j)} : Finset V) := by
    rw [he] at hve
    exact (mem_union.mp hve).resolve_right
      (fun hp => disjoint_left.mp (C.junction_private_disjoint e) hvJ hp)
  have hvf' : v ∈ ({C.junction k, C.junction (finRotate C.length k)} : Finset V) := by
    rw [hf] at hvf
    exact (mem_union.mp hvf).resolve_right
      (fun hp => disjoint_left.mp (C.junction_private_disjoint f) hvJ hp)
  have hji : j ≠ i := by
    intro h
    have hh := hj.symm.trans (h ▸ hi)
    cases hh
  have hki : k ≠ i := by
    intro h
    have hh := hk.symm.trans (h ▸ hi)
    cases hh
  rw [hm] at hvm
  simp only [mem_insert, mem_singleton] at hvm hve' hvf'
  have hjk : j = k := by
    rcases hvm with hm | hm
    · have hjrot : finRotate C.length j = i := by
        rcases hve' with he | he
        · exact False.elim (hji (C.junction_injective (he.symm.trans hm)))
        · exact C.junction_injective (he.symm.trans hm)
      have hkrot : finRotate C.length k = i := by
        rcases hvf' with hf | hf
        · exact False.elim (hki (C.junction_injective (hf.symm.trans hm)))
        · exact C.junction_injective (hf.symm.trans hm)
      exact (finRotate C.length).injective (hjrot.trans hkrot.symm)
    · have hje : j = finRotate C.length i := by
        rcases hve' with he | he
        · exact C.junction_injective (he.symm.trans hm)
        · exact False.elim (hji ((finRotate C.length).injective
            (C.junction_injective (he.symm.trans hm))))
      have hke : k = finRotate C.length i := by
        rcases hvf' with hf | hf
        · exact C.junction_injective (hf.symm.trans hm)
        · exact False.elim (hki ((finRotate C.length).injective
            (C.junction_injective (hf.symm.trans hm))))
      exact hje.trans hke.symm
  exact Sum.inr.inj (hj.symm.trans (hjk ▸ hk))

end MixedCycleOnWitness
end LooseHamilton
