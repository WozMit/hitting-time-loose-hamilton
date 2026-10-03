module

public import HittingTimeLooseHamilton.ActiveCycleNormalization

public section

/-! Local endpoint-cut classification on actual mixed-cycle witnesses. -/
noncomputable section
namespace LooseHamilton.MixedCycleOnWitness
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {r : ℕ} {S : Finset V} {markers edges : Finset (Finset V)}

/-- Marked slots cannot be consecutive because the prescribed pairs are disjoint. -/
theorem markers_not_consecutive (C : MixedCycleOnWitness r S markers edges)
    (i : Fin C.length) (e f : ↥markers)
    (he : C.slot i = Sum.inl e)
    (hf : C.slot (finRotate C.length i) = Sum.inl f) : False := by
  have hne : e.val ≠ f.val := by
    intro h
    have hs : e = f := Subtype.ext h
    have hi : i = finRotate C.length i := C.slot.injective (by rw [he, hf, hs])
    exact C.junction_next_ne i (congrArg C.junction hi)
  have hd : Disjoint e.val f.val := C.marked_matching e.property f.property hne
  have hleft := C.slot_edge i
  have hright := C.slot_edge (finRotate C.length i)
  rw [he] at hleft
  rw [hf] at hright
  simp only at hleft hright
  have hv1 : C.junction (finRotate C.length i) ∈ e.val := by rw [hleft]; simp
  have hv2 : C.junction (finRotate C.length i) ∈ f.val := by rw [hright]; simp
  exact disjoint_left.mp hd hv1 hv2

/-- An ordinary slot follows each marked slot. -/
theorem ordinary_after_marker (C : MixedCycleOnWitness r S markers edges)
    (i : Fin C.length) (e : ↥markers) (he : C.slot i = Sum.inl e) :
    ∃ f : ↥edges, C.slot (finRotate C.length i) = Sum.inr f := by
  cases hf : C.slot (finRotate C.length i) with
  | inl f => exact False.elim (C.markers_not_consecutive i e f he hf)
  | inr f => exact ⟨f, rfl⟩


/-- If an ordinary slot ends at a marked port, its next slot is that marker. -/
theorem marker_after_ordinary_of_port (C : MixedCycleOnWitness r S markers edges)
    (i : Fin C.length) (e : ↥edges) (hi : C.slot i = .inr e)
    (hp : C.junction (finRotate C.length i) ∈ originalPorts markers) :
    ∃ m : ↥markers, C.slot (finRotate C.length i) = .inl m := by
  obtain ⟨m, hm, hv⟩ := mem_biUnion.mp hp
  let m' : ↥markers := ⟨m, hm⟩
  let j := C.slot.symm (.inl m')
  have hs := C.slot_edge j
  have hj : C.slot j = .inl m' := C.slot.apply_symm_apply _
  rw [hj] at hs
  simp only at hs
  change C.junction (finRotate C.length i) ∈ m'.val at hv
  rw [hs] at hv
  rcases mem_insert.mp hv with h | h
  · have hij := C.junction_injective h
    exact ⟨m', hij ▸ hj⟩
  · have hij := (finRotate C.length).injective (C.junction_injective (mem_singleton.mp h))
    have hh := hi.symm.trans (hij ▸ hj)
    cases hh

/-- An allowed ordinary edge entering an original port exits at an ordinary vertex. -/
theorem ordinary_exit_not_port (C : MixedCycleOnWitness r S markers edges)
    (U : Finset V) (i : Fin C.length) (e : ↥edges)
    (hi : C.slot i = .inr e)
    (hallowed : (e.val ∩ U).card ≤ 1) (hu : C.junction i ∈ U) :
    C.junction (finRotate C.length i) ∉ U := by
  intro hv
  have hs := C.slot_edge i
  rw [hi] at hs
  simp only at hs
  have hp : {C.junction i, C.junction (finRotate C.length i)} ⊆ e.val ∩ U := by
    intro v h
    apply mem_inter.mpr
    constructor
    · rw [hs]; exact mem_union_left _ h
    · rcases mem_insert.mp h with rfl | h
      · exact hu
      · exact mem_singleton.mp h ▸ hv
  have hc := card_le_card hp
  rw [card_pair (C.junction_next_ne i)] at hc
  omega

/-- A marked root is followed by exactly one of the two endpoint-cut patterns.
The original-port set remains fixed throughout this classification. -/
theorem endpoint_cut_types (C : MixedCycleOnWitness r S markers edges)
    (hlarge : 6 ≤ C.length) (root : ↥markers) (U : Finset V)
    (hroot : C.slot ⟨0, by omega⟩ = .inl root)
    (hcover : U ⊆ originalPorts markers)
    (hold : ∀ m ∈ markers, m ≠ root.val → m ⊆ U)
    (hallowed : ∀ e ∈ edges, (e ∩ U).card ≤ 1) :
    ∃ e₁ : ↥edges, C.slot ⟨1, by omega⟩ = .inr e₁ ∧
      (C.junction ⟨2, by omega⟩ ∉ U ∨
        ∃ (m : ↥markers) (e₂ : ↥edges), m.val ≠ root.val ∧
          C.slot ⟨2, by omega⟩ = .inl m ∧
          C.slot ⟨3, by omega⟩ = .inr e₂ ∧
          C.junction ⟨4, by omega⟩ ∉ U) := by
  obtain ⟨e₁, he₁⟩ := C.ordinary_after_marker ⟨0, by omega⟩ root hroot
  rw [rotate_mk_succ (by omega)] at he₁
  refine ⟨e₁,he₁,?_⟩
  by_cases hu : C.junction ⟨2, by omega⟩ ∈ U
  · right
    have hp : C.junction (finRotate C.length ⟨1, by omega⟩) ∈ originalPorts markers := by
      rw [rotate_mk_succ (by omega)]
      exact hcover hu
    obtain ⟨m, hm⟩ := C.marker_after_ordinary_of_port ⟨1, by omega⟩ e₁ he₁ hp
    rw [rotate_mk_succ (by omega)] at hm
    have hmr : m.val ≠ root.val := by
      intro h
      have heq : m = root := Subtype.ext h
      have hidx := C.slot.injective (hm.trans (congrArg Sum.inl heq) |>.trans hroot.symm)
      have hbad : (2 : ℕ) = 0 := congrArg Fin.val hidx
      omega
    obtain ⟨e₂, he₂⟩ := C.ordinary_after_marker ⟨2, by omega⟩ m hm
    rw [rotate_mk_succ (by omega)] at he₂
    have hmu : C.junction ⟨3, by omega⟩ ∈ U := by
      apply hold m.val m.property hmr
      have hs := C.slot_edge ⟨2, by omega⟩
      rw [hm] at hs
      simp only at hs
      rw [hs, rotate_mk_succ (by omega)]
      simp
    have hout := C.ordinary_exit_not_port U ⟨3, by omega⟩ e₂ he₂
      (hallowed e₂.val e₂.property) hmu
    rw [rotate_mk_succ (by omega)] at hout
    exact ⟨m,e₂,hmr,hm,he₂,hout⟩
  · exact Or.inl hu

end LooseHamilton.MixedCycleOnWitness
