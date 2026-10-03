module

public import HittingTimeLooseHamilton.EndpointSurgerySlots

public section

/-! The exact edge and marker sets retained by the two local cuts. -/
noncomputable section
namespace LooseHamilton.MixedCycleOnWitness
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {r : ℕ} {S : Finset V} {M E : Finset (Finset V)}

/-- At a normalized Type I cut only the root marker is removed. -/
theorem prefixMarkers_one (C : MixedCycleOnWitness r S M E)
    (p : ↥M) (e : ↥E) (h₀ : C.slot ⟨0, by have := C.length_ge; omega⟩ = .inl p)
    (h₁ : C.slot ⟨1, by have := C.length_ge; omega⟩ = .inr e) :
    C.prefixMarkers 1 = M.erase p.val := by
  have hp : C.slot.symm (.inl p) = ⟨0, by have := C.length_ge; omega⟩ := C.slot.symm_apply_eq.mpr h₀.symm
  ext f
  rw [C.mem_prefixMarkers, mem_erase]
  constructor
  · rintro ⟨hf, hi⟩
    refine ⟨?_, hf⟩
    intro heq
    subst f
    simpa [hp] using hi
  · rintro ⟨hne, hf⟩
    refine ⟨hf, ?_⟩
    let i := C.slot.symm (.inl ⟨f, hf⟩)
    have hi : C.slot i = .inl ⟨f, hf⟩ := C.slot.apply_symm_apply _
    have hi₀ : i.val ≠ 0 := by
      intro h
      have he : i = ⟨0, by have := C.length_ge; omega⟩ := Fin.ext h
      rw [he, h₀] at hi
      exact hne (congrArg Subtype.val (Sum.inl.inj hi)).symm
    have hi₁ : i.val ≠ 1 := by
      intro h
      have he : i = ⟨1, by have := C.length_ge; omega⟩ := Fin.ext h
      rw [he, h₁] at hi
      cases hi
    change 1 < i.val
    omega

/-- At a normalized Type I cut only its first ordinary edge is removed. -/
theorem prefixEdges_one (C : MixedCycleOnWitness r S M E)
    (p : ↥M) (e : ↥E) (h₀ : C.slot ⟨0, by have := C.length_ge; omega⟩ = .inl p)
    (h₁ : C.slot ⟨1, by have := C.length_ge; omega⟩ = .inr e) :
    C.prefixEdges 1 = E.erase e.val := by
  have he : C.slot.symm (.inr e) = ⟨1, by have := C.length_ge; omega⟩ := C.slot.symm_apply_eq.mpr h₁.symm
  ext f
  rw [C.mem_prefixEdges, mem_erase]
  constructor
  · rintro ⟨hf, hi⟩
    refine ⟨?_, hf⟩
    intro heq
    subst f
    simpa [he] using hi
  · rintro ⟨hne, hf⟩
    refine ⟨hf, ?_⟩
    let i := C.slot.symm (.inr ⟨f, hf⟩)
    have hi : C.slot i = .inr ⟨f, hf⟩ := C.slot.apply_symm_apply _
    have hi₀ : i.val ≠ 0 := by
      intro h
      have he : i = ⟨0, by have := C.length_ge; omega⟩ := Fin.ext h
      rw [he, h₀] at hi
      cases hi
    have hi₁ : i.val ≠ 1 := by
      intro h
      have he : i = ⟨1, by have := C.length_ge; omega⟩ := Fin.ext h
      rw [he, h₁] at hi
      exact hne (congrArg Subtype.val (Sum.inr.inj hi)).symm
    change 1 < i.val
    omega

/-- Different slot contents force different inverse-slot indices. -/
theorem slot_index_ne (C : MixedCycleOnWitness r S M E)
    (i : Fin C.length) (s t : ↥M ⊕ ↥E) (hs : C.slot i = s) (hne : s ≠ t) :
    (C.slot.symm t).val ≠ i.val := by
  intro he
  have hi : C.slot.symm t = i := Fin.ext he
  have hh := C.slot.apply_symm_apply t
  rw [hi, hs] at hh
  exact hne hh

theorem prefixMarkers_three (C : MixedCycleOnWitness r S M E) (hn : 4 ≤ C.length)
    (p m : ↥M) (e f : ↥E)
    (h₀ : C.slot ⟨0, by omega⟩ = .inl p)
    (h₁ : C.slot ⟨1, by omega⟩ = .inr e)
    (h₂ : C.slot ⟨2, by omega⟩ = .inl m)
    (h₃ : C.slot ⟨3, by omega⟩ = .inr f) :
    C.prefixMarkers 3 = (M.erase p.val).erase m.val := by
  have hp : C.slot.symm (.inl p) = ⟨0, by omega⟩ := C.slot.symm_apply_eq.mpr h₀.symm
  have hm : C.slot.symm (.inl m) = ⟨2, by omega⟩ := C.slot.symm_apply_eq.mpr h₂.symm
  ext g
  rw [C.mem_prefixMarkers, mem_erase, mem_erase]
  constructor
  · rintro ⟨hg, hi⟩
    refine ⟨?_, ?_, hg⟩
    · intro heq; subst g; simpa [hm] using hi
    · intro heq; subst g; simpa [hp] using hi
  · rintro ⟨hgm, hgp, hg⟩
    refine ⟨hg, ?_⟩
    have h0 := C.slot_index_ne _ _ (.inl ⟨g,hg⟩) h₀ (by
      intro he; exact hgp (congrArg Subtype.val (Sum.inl.inj he)).symm)
    have h1 := C.slot_index_ne _ _ (.inl ⟨g,hg⟩) h₁ (by intro he; cases he)
    have h2 := C.slot_index_ne _ _ (.inl ⟨g,hg⟩) h₂ (by
      intro he; exact hgm (congrArg Subtype.val (Sum.inl.inj he)).symm)
    have h3 := C.slot_index_ne _ _ (.inl ⟨g,hg⟩) h₃ (by intro he; cases he)
    simp only at h0 h1 h2 h3
    omega

theorem prefixEdges_three (C : MixedCycleOnWitness r S M E) (hn : 4 ≤ C.length)
    (p m : ↥M) (e f : ↥E)
    (h₀ : C.slot ⟨0, by omega⟩ = .inl p)
    (h₁ : C.slot ⟨1, by omega⟩ = .inr e)
    (h₂ : C.slot ⟨2, by omega⟩ = .inl m)
    (h₃ : C.slot ⟨3, by omega⟩ = .inr f) :
    C.prefixEdges 3 = (E.erase e.val).erase f.val := by
  have he : C.slot.symm (.inr e) = ⟨1, by omega⟩ := C.slot.symm_apply_eq.mpr h₁.symm
  have hf : C.slot.symm (.inr f) = ⟨3, by omega⟩ := C.slot.symm_apply_eq.mpr h₃.symm
  ext g
  rw [C.mem_prefixEdges, mem_erase, mem_erase]
  constructor
  · rintro ⟨hg, hi⟩
    refine ⟨?_, ?_, hg⟩
    · intro heq; subst g; simpa [hf] using hi
    · intro heq; subst g; simpa [he] using hi
  · rintro ⟨hgf, hge, hg⟩
    refine ⟨hg, ?_⟩
    have h0 := C.slot_index_ne _ _ (.inr ⟨g,hg⟩) h₀ (by intro he; cases he)
    have h1 := C.slot_index_ne _ _ (.inr ⟨g,hg⟩) h₁ (by
      intro he; exact hge (congrArg Subtype.val (Sum.inr.inj he)).symm)
    have h2 := C.slot_index_ne _ _ (.inr ⟨g,hg⟩) h₂ (by intro he; cases he)
    have h3 := C.slot_index_ne _ _ (.inr ⟨g,hg⟩) h₃ (by
      intro he; exact hgf (congrArg Subtype.val (Sum.inr.inj he)).symm)
    simp only at h0 h1 h2 h3
    omega

end LooseHamilton.MixedCycleOnWitness
