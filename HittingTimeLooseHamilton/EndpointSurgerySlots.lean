module

public import HittingTimeLooseHamilton.EndpointSurgery

public section

noncomputable section
namespace LooseHamilton
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace MixedCycleOnWitness
variable {r : ℕ} {S : Finset V} {markers edges : Finset (Finset V)}

@[expose] def prefixMarkers (C : MixedCycleOnWitness r S markers edges) (k : ℕ) : Finset (Finset V) :=
  (univ.filter fun e : ↥markers => k < (C.slot.symm (.inl e)).val).image Subtype.val

@[expose] def prefixEdges (C : MixedCycleOnWitness r S markers edges) (k : ℕ) : Finset (Finset V) :=
  (univ.filter fun e : ↥edges => k < (C.slot.symm (.inr e)).val).image Subtype.val

@[simp] theorem mem_prefixMarkers (C : MixedCycleOnWitness r S markers edges)
    (k : ℕ) (e : Finset V) :
    e ∈ C.prefixMarkers k ↔ ∃ he : e ∈ markers, k < (C.slot.symm (.inl ⟨e,he⟩)).val := by
  simp only [prefixMarkers, mem_image, mem_filter, mem_univ, true_and]
  constructor
  · rintro ⟨f, hf, rfl⟩; exact ⟨f.property, hf⟩
  · rintro ⟨he, hh⟩; exact ⟨⟨e,he⟩, hh, rfl⟩

@[simp] theorem mem_prefixEdges (C : MixedCycleOnWitness r S markers edges)
    (k : ℕ) (e : Finset V) :
    e ∈ C.prefixEdges k ↔ ∃ he : e ∈ edges, k < (C.slot.symm (.inr ⟨e,he⟩)).val := by
  simp only [prefixEdges, mem_image, mem_filter, mem_univ, true_and]
  constructor
  · rintro ⟨f, hf, rfl⟩; exact ⟨f.property, hf⟩
  · rintro ⟨he, hh⟩; exact ⟨⟨e,he⟩, hh, rfl⟩

theorem prefixEdges_subset (C : MixedCycleOnWitness r S markers edges) (k : ℕ) :
    C.prefixEdges k ⊆ edges := fun e he => (C.mem_prefixEdges k e).mp he |>.choose

@[expose] def prefixKeep (C : MixedCycleOnWitness r S markers edges) (m k : ℕ)
    (hlen : C.length = m+k) : Fin m ↪ Fin C.length :=
  ⟨fun i => Fin.cast hlen.symm (endpointKeep m k i),
    (Fin.cast_injective _).comp (endpointKeep_injective m k)⟩

@[simp] theorem prefixKeep_val (C : MixedCycleOnWitness r S markers edges)
    (m k : ℕ) (hlen : C.length = m+k) (i : Fin m) :
    (C.prefixKeep m k hlen i).val = if i.val=0 then 0 else i.val+k := rfl

/-- Replace the prefix slots by a fresh marker, leaving every later slot alone. -/
@[expose] def prefixSlotMap (C : MixedCycleOnWitness r S markers edges)
    (m k : ℕ) (hlen : C.length = m+k) (q : Finset V) (i : Fin m) :
    ↥(insert q (C.prefixMarkers k)) ⊕ ↥(C.prefixEdges k) :=
  if hi : i.val=0 then .inl ⟨q, mem_insert_self _ _⟩
  else match hs : C.slot (C.prefixKeep m k hlen i) with
    | .inl e =>
      .inl ⟨e.val, mem_insert_of_mem ((C.mem_prefixMarkers k _).mpr
        ⟨e.property, by
          change k < (C.slot.symm (.inl e)).val
          rw [← hs, C.slot.symm_apply_apply, C.prefixKeep_val]
          simp only [hi, ↓reduceIte]
          omega⟩)⟩
    | .inr e =>
      .inr ⟨e.val, (C.mem_prefixEdges k _).mpr
        ⟨e.property, by
          change k < (C.slot.symm (.inr e)).val
          rw [← hs, C.slot.symm_apply_apply, C.prefixKeep_val]
          simp only [hi, ↓reduceIte]
          omega⟩⟩

/-- The source index can be read from every retained slot; the new marker has
no source index. -/
@[expose] def prefixSlotTrace (C : MixedCycleOnWitness r S markers edges)
    (k : ℕ) (q : Finset V) :
    (↥(insert q (C.prefixMarkers k)) ⊕ ↥(C.prefixEdges k)) → Option (Fin C.length)
  | .inl e => if h : e.val ∈ markers then some (C.slot.symm (.inl ⟨e.val,h⟩)) else none
  | .inr e => some (C.slot.symm (.inr ⟨e.val, (C.mem_prefixEdges k e.val).mp e.property |>.choose⟩))

theorem prefixSlotMap_trace (C : MixedCycleOnWitness r S markers edges)
    (m k : ℕ) (hlen : C.length = m+k) (q : Finset V) (hq : q ∉ markers)
    (i : Fin m) :
    C.prefixSlotTrace k q (C.prefixSlotMap m k hlen q i) =
      if i.val = 0 then none else some (C.prefixKeep m k hlen i) := by
  classical
  by_cases hi : i.val = 0
  · simp [prefixSlotMap, hi, prefixSlotTrace, hq]
  · simp only [prefixSlotMap, dif_neg hi, if_neg hi]
    split
    · rename_i e hs
      simp only [prefixSlotTrace, dif_pos e.property]
      congr 1
      exact (C.slot.symm_apply_eq).mpr hs.symm
    · rename_i e hs
      simp only [prefixSlotTrace]
      congr 1
      exact (C.slot.symm_apply_eq).mpr hs.symm

theorem prefixSlotMap_injective (C : MixedCycleOnWitness r S markers edges)
    (m k : ℕ) (hlen : C.length = m+k) (q : Finset V) (hq : q ∉ markers) :
    Function.Injective (C.prefixSlotMap m k hlen q) := by
  intro i j hij
  have ht := congrArg (C.prefixSlotTrace k q) hij
  rw [C.prefixSlotMap_trace m k hlen q hq, C.prefixSlotMap_trace m k hlen q hq] at ht
  split_ifs at ht with hi hj hj
  · exact Fin.ext (hi.trans hj.symm)
  · exact (C.prefixKeep m k hlen).injective (Option.some.inj ht)

theorem prefixSlotMap_surjective (C : MixedCycleOnWitness r S markers edges)
    (m k : ℕ) (hm : 0 < m) (hlen : C.length = m+k) (q : Finset V) :
    Function.Surjective (C.prefixSlotMap m k hlen q) := by
  intro e
  cases e with
  | inl e =>
    rcases mem_insert.mp e.property with he | he
    · refine ⟨⟨0,hm⟩, ?_⟩
      simp [prefixSlotMap, ← he]
    · obtain ⟨he', hh⟩ := (C.mem_prefixMarkers k e.val).mp he
      let j := C.slot.symm (.inl ⟨e.val,he'⟩)
      have hj : k < j.val := hh
      let i : Fin m := ⟨j.val-k, by have := j.isLt; omega⟩
      have hi : i.val ≠ 0 := by dsimp [i]; omega
      have hij : C.prefixKeep m k hlen i = j := by
        apply Fin.ext
        simp only [prefixKeep_val, hi, ↓reduceIte]
        dsimp [i]; omega
      have hs : C.slot (C.prefixKeep m k hlen i) = .inl ⟨e.val,he'⟩ := by
        rw [hij]; exact C.slot.apply_symm_apply _
      refine ⟨i, ?_⟩
      simp only [prefixSlotMap, dif_neg hi]
      split
      · rename_i f hf
        have heq := Sum.inl.inj (hf.symm.trans hs)
        cases heq
        rfl
      · rename_i f hf
        rw [hs] at hf
        contradiction
  | inr e =>
    obtain ⟨he', hh⟩ := (C.mem_prefixEdges k e.val).mp e.property
    let j := C.slot.symm (.inr ⟨e.val,he'⟩)
    have hj : k < j.val := hh
    let i : Fin m := ⟨j.val-k, by have := j.isLt; omega⟩
    have hi : i.val ≠ 0 := by dsimp [i]; omega
    have hij : C.prefixKeep m k hlen i = j := by
      apply Fin.ext
      simp only [prefixKeep_val, hi, ↓reduceIte]
      dsimp [i]; omega
    have hs : C.slot (C.prefixKeep m k hlen i) = .inr ⟨e.val,he'⟩ := by
      rw [hij]; exact C.slot.apply_symm_apply _
    refine ⟨i, ?_⟩
    simp only [prefixSlotMap, dif_neg hi]
    split
    · rename_i f hf
      rw [hs] at hf
      contradiction
    · rename_i f hf
      have heq := Sum.inr.inj (hf.symm.trans hs)
      cases heq
      rfl

@[expose] def prefixSlotEquiv (C : MixedCycleOnWitness r S markers edges)
    (m k : ℕ) (hm : 0 < m) (hlen : C.length = m+k) (q : Finset V) (hq : q ∉ markers) :
    Fin m ≃ (↥(insert q (C.prefixMarkers k)) ⊕ ↥(C.prefixEdges k)) :=
  Equiv.ofBijective (C.prefixSlotMap m k hlen q)
    ⟨C.prefixSlotMap_injective m k hlen q hq, C.prefixSlotMap_surjective m k hm hlen q⟩

@[simp] theorem prefixSlotEquiv_apply (C : MixedCycleOnWitness r S markers edges)
    (m k : ℕ) (hm : 0 < m) (hlen : C.length = m+k) (q : Finset V) (hq : q ∉ markers)
    (i : Fin m) : C.prefixSlotEquiv m k hm hlen q hq i = C.prefixSlotMap m k hlen q i := rfl

end MixedCycleOnWitness
end LooseHamilton
