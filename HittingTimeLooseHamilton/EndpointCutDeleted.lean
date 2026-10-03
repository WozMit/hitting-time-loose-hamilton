module

public import HittingTimeLooseHamilton.EndpointSurgeryCover
public import HittingTimeLooseHamilton.EndpointCutPrefix

public section

/-! The exact vertices removed by either endpoint cut. -/
noncomputable section
namespace LooseHamilton.MixedCycleOnWitness
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {r : ℕ} {S : Finset V} {M E : Finset (Finset V)}

theorem prefixInterior_one (C : MixedCycleOnWitness r S M E) :
    C.prefixInterior 1 = {C.junction ⟨1, by have := C.length_ge; omega⟩} := by
  ext v
  rw [C.mem_prefixInterior, mem_singleton]
  constructor
  · rintro ⟨i, hi, hik, hv⟩
    have he : i = ⟨1, by have := C.length_ge; omega⟩ := Fin.ext (by change i.val = 1; omega)
    simpa [he] using hv.symm
  · intro hv
    exact ⟨⟨1, by have := C.length_ge; omega⟩, by norm_num, by norm_num, hv.symm⟩

theorem prefixInterior_three (C : MixedCycleOnWitness r S M E) (hn : 4 ≤ C.length) :
    C.prefixInterior 3 = {C.junction ⟨1, by omega⟩, C.junction ⟨2, by omega⟩,
      C.junction ⟨3, by omega⟩} := by
  ext v
  rw [C.mem_prefixInterior]
  simp only [mem_insert, mem_singleton]
  constructor
  · rintro ⟨i, hi, hik, hv⟩
    have hc : i.val = 1 ∨ i.val = 2 ∨ i.val = 3 := by omega
    rcases hc with h | h | h
    · exact Or.inl (hv.symm.trans (congrArg C.junction (Fin.ext h)))
    · exact Or.inr (Or.inl (hv.symm.trans (congrArg C.junction (Fin.ext h))))
    · exact Or.inr (Or.inr (hv.symm.trans (congrArg C.junction (Fin.ext h))))
  · rintro (hv | hv | hv)
    · exact ⟨⟨1, by omega⟩, by norm_num, by norm_num, hv.symm⟩
    · exact ⟨⟨2, by omega⟩, by norm_num, by norm_num, hv.symm⟩
    · exact ⟨⟨3, by omega⟩, by norm_num, by norm_num, hv.symm⟩

theorem prefixRemovedPrivate_one (C : MixedCycleOnWitness r S M E)
    (p : ↥M) (e : ↥E) (h₀ : C.slot ⟨0, by have := C.length_ge; omega⟩ = .inl p)
    (h₁ : C.slot ⟨1, by have := C.length_ge; omega⟩ = .inr e) :
    C.prefixRemovedPrivate 1 = C.privateBlock e := by
  have hs := C.prefixEdges_one p e h₀ h₁
  have he : C.slot.symm (.inr e) = ⟨1, by have := C.length_ge; omega⟩ := C.slot.symm_apply_eq.mpr h₁.symm
  ext v
  rw [C.mem_prefixRemovedPrivate]
  constructor
  · rintro ⟨f, hf, hv⟩
    have hfe : f.val = e.val := by
      by_contra hne
      have hp : f.val ∈ C.prefixEdges 1 := by rw [hs]; exact mem_erase.mpr ⟨hne,f.property⟩
      have hh := (C.mem_prefixEdges 1 f.val).mp hp |>.choose_spec
      change 1 < (C.slot.symm (.inr f)).val at hh
      omega
    have hfe' : f = e := Subtype.ext hfe
    simpa [hfe'] using hv
  · intro hv
    exact ⟨e, by simp [he], hv⟩

theorem prefixRemovedPrivate_three (C : MixedCycleOnWitness r S M E) (hn : 4 ≤ C.length)
    (p m : ↥M) (e f : ↥E)
    (h₀ : C.slot ⟨0, by omega⟩ = .inl p)
    (h₁ : C.slot ⟨1, by omega⟩ = .inr e)
    (h₂ : C.slot ⟨2, by omega⟩ = .inl m)
    (h₃ : C.slot ⟨3, by omega⟩ = .inr f) :
    C.prefixRemovedPrivate 3 = C.privateBlock e ∪ C.privateBlock f := by
  have hs := C.prefixEdges_three hn p m e f h₀ h₁ h₂ h₃
  have he : C.slot.symm (.inr e) = ⟨1, by omega⟩ := C.slot.symm_apply_eq.mpr h₁.symm
  have hf : C.slot.symm (.inr f) = ⟨3, by omega⟩ := C.slot.symm_apply_eq.mpr h₃.symm
  ext v
  rw [C.mem_prefixRemovedPrivate, mem_union]
  constructor
  · rintro ⟨g, hg, hv⟩
    have hge : g.val = e.val ∨ g.val = f.val := by
      by_contra hne
      push_neg at hne
      have hp : g.val ∈ C.prefixEdges 3 := by
        rw [hs]; exact mem_erase.mpr ⟨hne.2, mem_erase.mpr ⟨hne.1,g.property⟩⟩
      have hh := (C.mem_prefixEdges 3 g.val).mp hp |>.choose_spec
      change 3 < (C.slot.symm (.inr g)).val at hh
      omega
    rcases hge with h | h
    · exact Or.inl (by simpa only [show g = e from Subtype.ext h] using hv)
    · exact Or.inr (by simpa only [show g = f from Subtype.ext h] using hv)
  · rintro (hv | hv)
    · exact ⟨e, by simp [he], hv⟩
    · exact ⟨f, by simp [hf], hv⟩

end LooseHamilton.MixedCycleOnWitness
