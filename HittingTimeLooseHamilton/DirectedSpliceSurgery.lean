module

public import HittingTimeLooseHamilton.DirectedSpliceIndex
public import HittingTimeLooseHamilton.ActiveCycleNormalization

public section

noncomputable section
open Finset
namespace LooseHamilton.MixedCycleOnWitness
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {r : ℕ} {S : Finset V} {M N E : Finset (Finset V)}

/-- Two marked cuts are reconnected by reversing the intervening arc.
The ordinary edges and their private blocks are preserved verbatim. -/
@[expose] def directedSplice (C : MixedCycleOnWitness r S M E)
    (j : Fin C.length) (hj : 0 < j.val)
    (p q : ↥M) (p' q' : ↥N) (σ : ↥M ≃ ↥N)
    (hp : C.slot ⟨0,by have := C.length_ge; omega⟩ = .inl p)
    (hq : C.slot j = .inl q)
    (hσp : σ p = p') (hσq : σ q = q')
    (hσ : ∀ m, m ≠ p → m ≠ q → (σ m).val = m.val)
    (hp' : p'.val = {C.junction ⟨0,by have := C.length_ge; omega⟩, C.junction j})
    (hq' : q'.val = {C.junction ⟨1,by have := C.length_ge; omega⟩,
      C.junction (finRotate C.length j)})
    (hN : (N : Set (Finset V)).PairwiseDisjoint id) :
    MixedCycleOnWitness r S N E := by
  have hn : 0 < C.length := by have := C.length_ge; omega
  let ρ := spliceJunctionIndex j
  let θ := spliceSlotIndex j
  let τ : (↥M ⊕ ↥E) ≃ (↥N ⊕ ↥E) := Equiv.sumCongr σ (Equiv.refl _)
  have hz : θ ⟨0,hn⟩ = ⟨0,hn⟩ := spliceSlotIndex_zero j hn
  have hjj : θ j = j := spliceSlotIndex_cut j
  have hnext : finRotate C.length ⟨0,hn⟩ = (⟨1,by have := C.length_ge; omega⟩ : Fin C.length) := by
    apply Fin.ext
    simp only [finRotate_val_eq C.length hn, show 1 < C.length by have := C.length_ge; omega, ↓reduceIte]
  refine {
    length := C.length
    length_ge := C.length_ge
    junction := fun i => C.junction (ρ i)
    junction_injective := C.junction_injective.comp ρ.injective
    junction_next_ne := ?_
    slot := θ.trans (C.slot.trans τ)
    privateBlock := C.privateBlock
    private_card := C.private_card
    private_disjoint := C.private_disjoint
    junction_private_disjoint := ?_
    cover := ?_
    marked_matching := hN
    slot_edge := ?_ }
  · intro i h
    exact C.junction_next_ne i (congrArg C.junction (ρ.injective (C.junction_injective h)))
  · intro e
    apply (C.junction_private_disjoint e).mono_left
    intro v hv
    obtain ⟨i, _, rfl⟩ := mem_image.mp hv
    exact mem_image_of_mem _ (mem_univ _)
  · apply C.cover.trans
    congr 1
    ext v
    simp only [mem_image, mem_univ, true_and]
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨ρ.symm i, by simp⟩
    · rintro ⟨i, rfl⟩
      exact ⟨ρ i, rfl⟩
  · intro i
    change (match τ (C.slot (θ i)) with
      | .inl e => e.val = {C.junction (ρ i), C.junction (ρ (finRotate C.length i))}
      | .inr e => e.val = {C.junction (ρ i), C.junction (ρ (finRotate C.length i))} ∪ C.privateBlock e)
    by_cases hi0 : i = ⟨0,hn⟩
    · subst i
      rw [hz, hp]
      change (σ p).val = _
      rw [hσp, hp']
      simp only [ρ, spliceJunctionIndex_zero, hnext, spliceJunctionIndex_one j hj]
    by_cases hij : i = j
    · subst i
      rw [hjj, hq]
      change (σ q).val = _
      rw [hσq, hq']
      simp only [ρ, spliceJunctionIndex_cut j hj, spliceJunctionIndex_cut_next j hj]
    have hθ0 : θ i ≠ ⟨0,hn⟩ := by
      intro h
      exact hi0 (θ.injective (h.trans hz.symm))
    have hθj : θ i ≠ j := by
      intro h
      exact hij (θ.injective (h.trans hjj.symm))
    have hpair : ({C.junction (ρ i), C.junction (ρ (finRotate C.length i))} : Finset V) =
        {C.junction (θ i), C.junction (finRotate C.length (θ i))} := by
      by_cases hlt : i.val < j.val
      · have hh := splice_indices_internal j i (by
          have : i.val ≠ 0 := fun h => hi0 (Fin.ext h)
          omega) hlt
        rw [show ρ i = finRotate C.length (θ i) from hh.1,
          show ρ (finRotate C.length i) = θ i from hh.2]
        exact pair_comm _ _
      · have hh := splice_indices_external j i hj (by
          have : i.val ≠ j.val := fun h => hij (Fin.ext h)
          omega)
        rw [show ρ i = θ i from hh.1,
          show ρ (finRotate C.length i) = finRotate C.length (θ i) from hh.2]
    have hs := C.slot_edge (θ i)
    cases he : C.slot (θ i) with
    | inl m =>
      rw [he] at hs
      change (σ m).val = _
      rw [hσ m (by intro h; subst m; exact hθ0 (C.slot.injective (he.trans hp.symm)))
        (by intro h; subst m; exact hθj (C.slot.injective (he.trans hq.symm))), hpair]
      exact hs
    | inr e =>
      rw [he] at hs
      change e.val = _
      rw [hpair]
      exact hs

section Directions
variable (C : MixedCycleOnWitness r S M E)
    (j : Fin C.length) (hj : 0 < j.val)
    (p q : ↥M) (p' q' : ↥N) (σ : ↥M ≃ ↥N)
    (hp : C.slot ⟨0,by have := C.length_ge; omega⟩ = .inl p)
    (hq : C.slot j = .inl q)
    (hσp : σ p = p') (hσq : σ q = q')
    (hσ : ∀ m, m ≠ p → m ≠ q → (σ m).val = m.val)
    (hp' : p'.val = {C.junction ⟨0,by have := C.length_ge; omega⟩, C.junction j})
    (hq' : q'.val = {C.junction ⟨1,by have := C.length_ge; omega⟩,
      C.junction (finRotate C.length j)})
    (hN : (N : Set (Finset V)).PairwiseDisjoint id)

local notation "D" => C.directedSplice j hj p q p' q' σ hp hq hσp hσq hσ hp' hq' hN

theorem directedSplice_first_position :
    (D).slot.symm (.inl p') = ⟨0, by change 0 < C.length; have := C.length_ge; omega⟩ := by
  apply (D).slot.symm_apply_eq.mpr
  change .inl p' = (Equiv.sumCongr σ (Equiv.refl ↥E))
    (C.slot (spliceSlotIndex j ⟨0,by have := C.length_ge; omega⟩))
  rw [spliceSlotIndex_zero, hp]
  change Sum.inl p' = Sum.inl (σ p)
  rw [hσp]

theorem directedSplice_second_position : (D).slot.symm (.inl q') = j := by
  apply (D).slot.symm_apply_eq.mpr
  change .inl q' = (Equiv.sumCongr σ (Equiv.refl ↥E))
    (C.slot (spliceSlotIndex j j))
  rw [spliceSlotIndex_cut, hq]
  change Sum.inl q' = Sum.inl (σ q)
  rw [hσq]

/-- After reversal the first replacement marker is traversed from old `v` to old `a`. -/
theorem directedSplice_reverse_first_start :
    (D).reverse.junction ((D).reverse.slot.symm (.inl p')) = C.junction j := by
  rw [reverse_slot_start, directedSplice_first_position]
  change C.junction (spliceJunctionIndex j (finRotate C.length ⟨0,by have := C.length_ge; omega⟩)) = _
  have hn : 0 < C.length := by have := C.length_ge; omega
  have he : finRotate C.length ⟨0,hn⟩ = (⟨1,by have := C.length_ge; omega⟩ : Fin C.length) := by
    apply Fin.ext
    simp only [finRotate_val_eq C.length hn, show 1 < C.length by have := C.length_ge; omega, ↓reduceIte]
  rw [he, spliceJunctionIndex_one j hj]

theorem directedSplice_reverse_first_end :
    (D).reverse.junction (finRotate (D).reverse.length ((D).reverse.slot.symm (.inl p'))) =
      C.junction ⟨0,by have := C.length_ge; omega⟩ := by
  rw [reverse_slot_end, directedSplice_first_position]
  change C.junction (spliceJunctionIndex j ⟨0,by have := C.length_ge; omega⟩) = _
  rw [spliceJunctionIndex_zero]

/-- The other replacement marker is traversed from old `t` to old `z`. -/
theorem directedSplice_reverse_second_start :
    (D).reverse.junction ((D).reverse.slot.symm (.inl q')) =
      C.junction (finRotate C.length j) := by
  rw [reverse_slot_start, directedSplice_second_position]
  change C.junction (spliceJunctionIndex j (finRotate C.length j)) = _
  rw [spliceJunctionIndex_cut_next j hj]

theorem directedSplice_reverse_second_end :
    (D).reverse.junction (finRotate (D).reverse.length ((D).reverse.slot.symm (.inl q'))) =
      C.junction ⟨1,by have := C.length_ge; omega⟩ := by
  rw [reverse_slot_end, directedSplice_second_position]
  change C.junction (spliceJunctionIndex j j) = _
  rw [spliceJunctionIndex_cut j hj]
/-- The surgery preserves every ordinary edge's assigned private vertices. -/
@[simp] theorem directedSplice_privateBlock (e : ↥E) :
    (D).privateBlock e = C.privateBlock e := rfl

@[simp] theorem directedSplice_reverse_privateBlock (e : ↥E) :
    (D).reverse.privateBlock e = C.privateBlock e := rfl
end Directions
end LooseHamilton.MixedCycleOnWitness
