module

public import HittingTimeLooseHamilton.DirectedSpliceSurgery
public import HittingTimeLooseHamilton.SpliceMarkerExchange
public import HittingTimeLooseHamilton.ActiveDirectedCompletions
public import HittingTimeLooseHamilton.ActiveOrientationUniqueness

public section

/-! Exchange the two directed cut markers, keeping one cyclic component. -/
noncomputable section
namespace LooseHamilton
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The two directed markers `a→z` and `v→t` can be exchanged for
`t→z` and `v→a` without changing any ordinary edge or active vertex. -/
theorem directed_marker_exchange {r : ℕ} {S : Finset V}
    {M E : Finset (Finset V)} {a z v t : V}
    (hr : 3 ≤ r) (haz : a ≠ z) (hvt : v ≠ t)
    (hp : ({a,z} : Finset V) ∉ insert {v,t} M) (hq : ({v,t} : Finset V) ∉ M)
    (hp' : ({a,v} : Finset V) ∉ insert {z,t} M) (hq' : ({z,t} : Finset V) ∉ M)
    (hN : ((insert ({a,v} : Finset V) (insert {z,t} M) : Finset (Finset V)) : Set (Finset V)).PairwiseDisjoint id)
    (h : rootedDirectedCycleOn r S (insert {a,z} (insert {v,t} M)) E
      ⟨{a,z}, mem_insert_self _ _⟩
      ⟨{v,t}, mem_insert_of_mem (mem_insert_self _ _)⟩ a v) :
    rootedDirectedCycleOn r S (insert {a,v} (insert {z,t} M)) E
      ⟨{z,t}, mem_insert_of_mem (mem_insert_self _ _)⟩
      ⟨{a,v}, mem_insert_self _ _⟩ t v := by
  let p : ↥(insert ({a,z} : Finset V) (insert {v,t} M)) := ⟨{a,z}, mem_insert_self _ _⟩
  let q : ↥(insert ({a,z} : Finset V) (insert {v,t} M)) :=
    ⟨{v,t}, mem_insert_of_mem (mem_insert_self _ _)⟩
  let p' : ↥(insert ({a,v} : Finset V) (insert {z,t} M)) := ⟨{a,v}, mem_insert_self _ _⟩
  let q' : ↥(insert ({a,v} : Finset V) (insert {z,t} M)) :=
    ⟨{z,t}, mem_insert_of_mem (mem_insert_self _ _)⟩
  obtain ⟨C, ha, hv⟩ := h
  obtain ⟨D, hzero, hstart, hend⟩ := C.exists_rooted p a z rfl haz
  have hroot : D.junction (D.slot.symm (.inl p)) = a := by
    rw [show D.slot.symm (.inl p) = ⟨0,by have := D.length_ge; omega⟩ from
      D.slot.symm_apply_eq.mpr hzero.symm]
    exact hstart
  have hvD : D.junction (D.slot.symm (.inl q)) = v :=
    (D.slot_start_eq_of_root C hr p (hroot.trans ha.symm) (.inl q)).trans hv
  let j := D.slot.symm (.inl q)
  have hj : 0 < j.val := by
    by_contra hn
    have he : j = ⟨0,by have := D.length_ge; omega⟩ := Fin.ext (by simpa only [Fin.val_mk] using Nat.eq_zero_of_not_pos hn)
    have heq : p = q := Sum.inl.inj (hzero.symm.trans (he ▸ D.slot.apply_symm_apply (.inl q)))
    exact hp (by rw [show ({a,z} : Finset V) = {v,t} from congrArg Subtype.val heq]; simp)
  have htD : D.junction (finRotate D.length j) = t := by
    have hs := D.slot_edge j
    rw [D.slot.apply_symm_apply] at hs
    change ({v,t} : Finset V) = {D.junction j, D.junction (finRotate D.length j)} at hs
    rw [hvD] at hs
    have ht : t ∈ ({v,t} : Finset V) := by simp
    rw [hs] at ht
    exact (mem_singleton.mp ((mem_insert.mp ht).resolve_left (Ne.symm hvt))).symm
  let σ := exchangeTwoInsertedEquiv M ({a,z} : Finset V) {v,t} {a,v} {z,t} hp hq hp' hq'
  have hσp : σ p = p' := exchangeTwoInsertedEquiv_first _ _ _ _ _ _ _ _ _
  have hσq : σ q = q' := exchangeTwoInsertedEquiv_second _ _ _ _ _ _ _ _ _
  have hσ : ∀ m, m ≠ p → m ≠ q → (σ m).val = m.val := by
    intro m hmp hmq
    have hm : m.val ∈ M := by
      have hh := m.property
      rcases mem_insert.mp hh with hh | hh
      · exact False.elim (hmp (Subtype.ext hh))
      · rcases mem_insert.mp hh with hh | hh
        · exact False.elim (hmq (Subtype.ext hh))
        · exact hh
    exact congrArg Subtype.val (exchangeTwoInsertedEquiv_old M _ _ _ _ hp hq hp' hq' ⟨m.val,hm⟩)
  have heqp : p'.val = {D.junction ⟨0,by have := D.length_ge; omega⟩, D.junction j} := by
    change {a,v} = _
    rw [hstart, hvD]
  have heqq : q'.val = {D.junction ⟨1,by have := D.length_ge; omega⟩,
      D.junction (finRotate D.length j)} := by
    change {z,t} = _
    rw [hend, htD]
  let A := D.directedSplice j hj p q p' q' σ hzero (D.slot.apply_symm_apply (.inl q))
    hσp hσq hσ heqp heqq hN
  refine ⟨A.reverse, ?_, ?_⟩
  · exact (D.directedSplice_reverse_second_start j hj p q p' q' σ hzero
      (D.slot.apply_symm_apply (.inl q)) hσp hσq hσ heqp heqq hN).trans htD
  · exact (D.directedSplice_reverse_first_start j hj p q p' q' σ hzero
      (D.slot.apply_symm_apply (.inl q)) hσp hσq hσ heqp heqq hN).trans hvD

/-- Put the distinguished directed marker in position zero while retaining the
prescribed root direction. -/
theorem rootedDirectedCycleOn_normalize_distinguished {r : ℕ} {S : Finset V}
    {M E : Finset (Finset V)} (hr : 3 ≤ r)
    (root distinguished : ↥M) {a v w : V} (hvw : v ≠ w)
    (hpair : distinguished.val = {v,w})
    (h : rootedDirectedCycleOn r S M E root distinguished a v) :
    ∃ C : MixedCycleOnWitness r S M E,
      C.slot ⟨0, by have := C.length_ge; omega⟩ = .inl distinguished ∧
      C.junction ⟨0, by have := C.length_ge; omega⟩ = v ∧
      C.junction ⟨1, by have := C.length_ge; omega⟩ = w ∧
      C.junction (C.slot.symm (.inl root)) = a := by
  obtain ⟨C, ha, hv⟩ := h
  obtain ⟨D, hs, h0, h1⟩ := C.exists_rooted distinguished v w hpair hvw
  have hd : D.junction (D.slot.symm (.inl distinguished)) = v := by
    rw [show D.slot.symm (.inl distinguished) = ⟨0,by have := D.length_ge; omega⟩ from
      D.slot.symm_apply_eq.mpr hs.symm]
    exact h0
  exact ⟨D, hs, h0, h1,
    (D.slot_start_eq_of_root C hr distinguished (hd.trans hv.symm) (.inl root)).trans ha⟩

/-- The exchanged cycle, positioned for restoring the cut path. -/
theorem directed_marker_exchange_normalized {r : ℕ} {S : Finset V}
    {M E : Finset (Finset V)} {a z v t : V}
    (hr : 3 ≤ r) (haz : a ≠ z) (hvt : v ≠ t) (hva : v ≠ a)
    (hp : ({a,z} : Finset V) ∉ insert {v,t} M) (hq : ({v,t} : Finset V) ∉ M)
    (hp' : ({a,v} : Finset V) ∉ insert {z,t} M) (hq' : ({z,t} : Finset V) ∉ M)
    (hN : ((insert ({a,v} : Finset V) (insert {z,t} M) : Finset (Finset V)) : Set (Finset V)).PairwiseDisjoint id)
    (h : rootedDirectedCycleOn r S (insert {a,z} (insert {v,t} M)) E
      ⟨{a,z}, mem_insert_self _ _⟩
      ⟨{v,t}, mem_insert_of_mem (mem_insert_self _ _)⟩ a v) :
    ∃ C : MixedCycleOnWitness r S (insert {v,a} (insert {t,z} M)) E,
      C.slot ⟨0, by have := C.length_ge; omega⟩ = .inl ⟨{v,a}, mem_insert_self _ _⟩ ∧
      C.junction ⟨0, by have := C.length_ge; omega⟩ = v ∧
      C.junction ⟨1, by have := C.length_ge; omega⟩ = a ∧
      C.junction (C.slot.symm (.inl ⟨{t,z}, mem_insert_of_mem (mem_insert_self _ _)⟩)) = t := by
  have hd := directed_marker_exchange hr haz hvt hp hq hp' hq' hN h
  have hd' : rootedDirectedCycleOn r S (insert {v,a} (insert {t,z} M)) E
      ⟨{t,z}, mem_insert_of_mem (mem_insert_self _ _)⟩
      ⟨{v,a}, mem_insert_self _ _⟩ t v := by
    apply (rootedDirectedCycleOn_congr
      (show insert ({a,v} : Finset V) (insert {z,t} M) = insert {v,a} (insert {t,z} M) by
        rw [pair_comm a v, pair_comm z t]) rfl _ _ _ _ (pair_comm z t) (pair_comm a v) t v).mp hd
  exact rootedDirectedCycleOn_normalize_distinguished hr _ _ hva rfl hd'

end LooseHamilton
