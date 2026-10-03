module

public import HittingTimeLooseHamilton.CycleOn
public import HittingTimeLooseHamilton.SlotTransfer
public import HittingTimeLooseHamilton.Models

public section
noncomputable section
namespace LooseHamilton
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace MixedCycleOnWitness
variable {r : ℕ} {S : Finset V} {markers edges : Finset (Finset V)}
@[expose] def endpointPair (C : MixedCycleOnWitness r S markers edges) (e : ↥edges) : Finset V :=
  {C.junction (C.slot.symm (.inr e)),
    C.junction (finRotate C.length (C.slot.symm (.inr e)))}

theorem edge_eq_endpointPair (C : MixedCycleOnWitness r S markers edges) (e : ↥edges) :
    e.val = C.endpointPair e ∪ C.privateBlock e := by
  have h := C.slot_edge (C.slot.symm (.inr e))
  simpa [endpointPair] using h

theorem endpointPair_card (C : MixedCycleOnWitness r S markers edges) (e : ↥edges) :
    (C.endpointPair e).card = 2 := by
  exact card_pair (C.junction_next_ne _)

theorem endpointPair_subset_junctions (C : MixedCycleOnWitness r S markers edges)
    (e : ↥edges) : C.endpointPair e ⊆ univ.image C.junction := by
  intro v hv
  simp only [endpointPair, mem_insert, mem_singleton] at hv
  rcases hv with rfl | rfl <;> exact mem_image_of_mem _ (mem_univ _)

theorem endpointPair_private_disjoint (C : MixedCycleOnWitness r S markers edges)
    (e : ↥edges) : Disjoint (C.endpointPair e) (C.privateBlock e) :=
  (C.junction_private_disjoint e).mono_left (C.endpointPair_subset_junctions e)

theorem other_edge_private_disjoint (C : MixedCycleOnWitness r S markers edges)
    (e f : ↥edges) (hef : f ≠ e) : Disjoint f.val (C.privateBlock e) := by
  rw [C.edge_eq_endpointPair f, disjoint_union_left]
  exact ⟨(C.junction_private_disjoint e).mono_left (C.endpointPair_subset_junctions f),
    C.private_disjoint hef⟩

theorem marked_private_disjoint (C : MixedCycleOnWitness r S markers edges)
    (e : ↥edges) (m : ↥markers) : Disjoint m.val (C.privateBlock e) := by
  have h := C.slot_edge (C.slot.symm (.inl m))
  simp only [C.slot.apply_symm_apply] at h
  rw [h]
  apply (C.junction_private_disjoint e).mono_left
  intro v hv
  simp only [endpointPair, mem_insert, mem_singleton] at hv
  rcases hv with rfl | rfl <;> exact mem_image_of_mem _ (mem_univ _)

@[expose] def contract (C : MixedCycleOnWitness r S markers edges) (e : ↥edges)
    (hp : C.endpointPair e ∉ markers)
    (hm : ((insert (C.endpointPair e) markers : Finset (Finset V)) : Set (Finset V)).PairwiseDisjoint id) :
    MixedCycleOnWitness r (S \ C.privateBlock e)
      (insert (C.endpointPair e) markers) (edges.erase e.val) where
  length := C.length
  length_ge := C.length_ge
  junction := C.junction
  junction_injective := C.junction_injective
  junction_next_ne := C.junction_next_ne
  slot := C.slot.trans (slotTransfer markers edges (C.endpointPair e) e.val hp e.property)
  privateBlock f := C.privateBlock ⟨f, (mem_erase.mp f.property).2⟩
  private_card f := C.private_card _
  private_disjoint := by
    intro a b hab
    apply C.private_disjoint
    intro h
    apply hab
    exact Subtype.ext (congrArg (fun x : ↥edges => x.val) h)
  junction_private_disjoint f := C.junction_private_disjoint _
  cover := by
    ext v
    simp only [mem_sdiff, mem_union]
    rw [show v ∈ S ↔ v ∈ univ.image C.junction ∪ univ.biUnion C.privateBlock from by rw [← C.cover]]
    simp only [mem_sdiff, mem_union, mem_biUnion, mem_univ, true_and]
    constructor
    · rintro ⟨h, hn⟩
      rcases h with h | ⟨f,hf⟩
      · exact Or.inl h
      · right
        have hfe : f.val ≠ e.val := by
          intro heq
          have : f = e := Subtype.ext heq
          subst f
          exact hn hf
        exact ⟨⟨f, mem_erase.mpr ⟨hfe, f.property⟩⟩, hf⟩
    · intro h
      rcases h with h | ⟨f,hf⟩
      · exact ⟨Or.inl h, fun hv => disjoint_left.mp (C.junction_private_disjoint e) h hv⟩
      · let f' : ↥edges := ⟨f, (mem_erase.mp f.property).2⟩
        have hfe : f' ≠ e := by
          intro h
          exact (mem_erase.mp f.property).1 (congrArg (fun x : ↥edges => x.val) h)
        exact ⟨Or.inr ⟨f',hf⟩, fun hv => disjoint_left.mp (C.private_disjoint hfe) hf hv⟩
  marked_matching := hm
  slot_edge := by
    intro i
    have h := C.slot_edge i
    dsimp only [Equiv.trans_apply, slotTransfer, Equiv.sumComm_apply]
    cases hs : C.slot i with
    | inl a => simpa [Equiv.trans_apply, hs, slotTransfer] using h
    | inr b =>
      by_cases hb : b.val = e.val
      · have hbe : b = e := Subtype.ext hb
        have hi : i = C.slot.symm (.inr e) := C.slot.injective (by simpa [hbe] using hs)
        subst i
        simp only [Equiv.coe_fn_mk, hb, ↓reduceDIte]
        rfl
      · have hbe : b ≠ e := fun he => hb (congrArg Subtype.val he)
        simpa [hs, hb, hbe] using h

theorem endpointPair_subset_edge (C : MixedCycleOnWitness r S markers edges)
    (e : ↥edges) : C.endpointPair e ⊆ e.val := by
  rw [C.edge_eq_endpointPair e]
  exact subset_union_left

theorem endpointPair_disjoint_marker (C : MixedCycleOnWitness r S markers edges)
    (e : ↥edges) (he : Disjoint e.val (originalPorts markers))
    (m : Finset V) (hm : m ∈ markers) : Disjoint (C.endpointPair e) m := by
  apply he.mono (C.endpointPair_subset_edge e)
  intro v hv
  exact mem_biUnion.mpr ⟨m,hm,hv⟩

theorem endpointPair_not_mem_markers (C : MixedCycleOnWitness r S markers edges)
    (e : ↥edges) (he : Disjoint e.val (originalPorts markers)) :
    C.endpointPair e ∉ markers := by
  intro hm
  have hd := C.endpointPair_disjoint_marker e he _ hm
  have hz := disjoint_self.mp hd
  have hc := C.endpointPair_card e
  rw [hz] at hc
  simp at hc

theorem insert_endpointPair_matching (C : MixedCycleOnWitness r S markers edges)
    (e : ↥edges) (he : Disjoint e.val (originalPorts markers)) :
    ((insert (C.endpointPair e) markers : Finset (Finset V)) : Set (Finset V)).PairwiseDisjoint id := by
  intro a ha b hb hab
  rcases mem_insert.mp ha with rfl | ha <;> rcases mem_insert.mp hb with rfl | hb
  · exact False.elim (hab rfl)
  · exact C.endpointPair_disjoint_marker e he b hb
  · exact (C.endpointPair_disjoint_marker e he a ha).symm
  · exact C.marked_matching ha hb hab

/-- Contract an edge avoiding every old marked vertex. -/
@[expose] def contractUnmarked (C : MixedCycleOnWitness r S markers edges)
    (e : ↥edges) (he : Disjoint e.val (originalPorts markers)) :
    MixedCycleOnWitness r (S \ C.privateBlock e)
      (insert (C.endpointPair e) markers) (edges.erase e.val) :=
  C.contract e (C.endpointPair_not_mem_markers e he) (C.insert_endpointPair_matching e he)

/-- Replace one marked pair by an ordinary edge with new private vertices. -/
@[expose] def expand (C : MixedCycleOnWitness r S markers edges) (p : ↥markers)
    (P : Finset V) (hP : P.card = r - 2) (hPS : Disjoint P S)
    (hE : p.val ∪ P ∉ edges) :
    MixedCycleOnWitness r (S ∪ P) (markers.erase p.val) (insert (p.val ∪ P) edges) where
  length := C.length
  length_ge := C.length_ge
  junction := C.junction
  junction_injective := C.junction_injective
  junction_next_ne := C.junction_next_ne
  slot := ((C.slot.trans (Equiv.sumComm _ _)).trans
    (slotTransfer edges markers (p.val ∪ P) p.val hE p.property)).trans (Equiv.sumComm _ _)
  privateBlock f := if h : f.val = p.val ∪ P then P
    else C.privateBlock ⟨f, (mem_insert.mp f.property).resolve_left h⟩
  private_card f := by split <;> first | exact hP | exact C.private_card _
  private_disjoint := by
    intro a b hab
    split_ifs with ha hb hb
    · exact False.elim (hab (Subtype.ext (ha.trans hb.symm)))
    · exact hPS.mono_right (C.private_subset_active _)
    · exact (hPS.mono_right (C.private_subset_active _)).symm
    · apply C.private_disjoint
      intro h
      exact hab (Subtype.ext (congrArg (fun x : ↥edges => x.val) h))
  junction_private_disjoint f := by
    split_ifs
    · apply hPS.symm.mono_left
      intro v hv
      obtain ⟨i,_,rfl⟩ := mem_image.mp hv
      exact C.junction_mem i
    · exact C.junction_private_disjoint _
  cover := by
    ext v
    simp only [mem_sdiff, mem_union]
    rw [show v ∈ S ↔ v ∈ univ.image C.junction ∪ univ.biUnion C.privateBlock from by rw [← C.cover]]
    simp only [mem_union, mem_biUnion, mem_univ, true_and]
    constructor
    · rintro ((h | ⟨f,hf⟩) | h)
      · exact Or.inl h
      · right
        refine ⟨⟨f, mem_insert_of_mem f.property⟩, ?_⟩
        have hn : f.val ≠ p.val ∪ P := by intro h; exact hE (h ▸ f.property)
        simp only [hn, ↓reduceDIte]
        exact hf
      · right
        exact ⟨⟨p.val ∪ P, mem_insert_self _ _⟩, by simpa using h⟩
    · rintro (h | ⟨f,hf⟩)
      · exact Or.inl (Or.inl h)
      · split_ifs at hf with h
        · exact Or.inr hf
        · exact Or.inl (Or.inr ⟨_,hf⟩)
  marked_matching := by
    intro a ha b hb hab
    exact C.marked_matching (mem_erase.mp ha).2 (mem_erase.mp hb).2 hab
  slot_edge := by
    intro i
    have h := C.slot_edge i
    dsimp only [Equiv.trans_apply, slotTransfer, Equiv.sumComm_apply]
    cases hs : C.slot i with
    | inl a =>
      by_cases ha : a.val = p.val
      · have hap : a = p := Subtype.ext ha
        have hp := h
        simp only [hs] at hp
        simp only [hap] at hp
        simpa [Equiv.trans_apply, hs, slotTransfer, ha, hap] using congrArg (fun q => q ∪ P) hp
      · have hap : a ≠ p := fun he => ha (congrArg Subtype.val he)
        simpa [hs, ha, hap] using h
    | inr b =>
      have hb : b.val ≠ p.val ∪ P := by intro h; exact hE (h ▸ b.property)
      simpa [Equiv.trans_apply, hs, slotTransfer, hb] using h

@[simp] theorem expand_privateBlock (C : MixedCycleOnWitness r S markers edges) (p : ↥markers)
    (P : Finset V) (hP : P.card = r - 2) (hPS : Disjoint P S)
    (hE : p.val ∪ P ∉ edges) :
    (C.expand p P hP hPS hE).privateBlock ⟨p.val ∪ P, mem_insert_self _ _⟩ = P := by
  simp [expand]

@[simp] theorem expand_endpointPair (C : MixedCycleOnWitness r S markers edges) (p : ↥markers)
    (P : Finset V) (hP : P.card = r - 2) (hPS : Disjoint P S)
    (hE : p.val ∪ P ∉ edges) :
    (C.expand p P hP hPS hE).endpointPair ⟨p.val ∪ P, mem_insert_self _ _⟩ = p.val := by
  have h := C.slot_edge (C.slot.symm (.inl p))
  simp only [C.slot.apply_symm_apply] at h
  change {C.junction (((slotTransfer edges markers (p.val ∪ P) p.val hE p.property).symm (.inl ⟨p.val ∪ P, mem_insert_self _ _⟩)).swap |> C.slot.symm),
    C.junction (finRotate C.length (((slotTransfer edges markers (p.val ∪ P) p.val hE p.property).symm (.inl ⟨p.val ∪ P, mem_insert_self _ _⟩)).swap |> C.slot.symm))} = _
  simpa only [slotTransfer, Equiv.coe_fn_symm_mk, ↓reduceDIte, Sum.swap_inr] using h.symm
end MixedCycleOnWitness
end LooseHamilton
