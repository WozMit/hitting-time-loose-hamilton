module

public import HittingTimeLooseHamilton.CycleOn

public section

/-! # Restriction to an active vertex set

The ambient formulation is equivalent to the original spanning-cycle definition
on the subtype of active vertices. No cycle condition is lost by using it.
-/
namespace LooseHamilton
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

@[expose] def restrictEdge (S e : Finset V) : Finset ↥S := univ.filter (fun x => x.val ∈ e)
@[expose] def liftEdge (S : Finset V) (e : Finset ↥S) : Finset V := e.image Subtype.val
@[expose] def restrictEdges (S : Finset V) (E : Finset (Finset V)) := E.image (restrictEdge S)

@[simp] theorem mem_restrictEdge (S e : Finset V) (x : ↥S) :
    x ∈ restrictEdge S e ↔ x.val ∈ e := by simp [restrictEdge]

@[simp] theorem lift_restrictEdge (S e : Finset V) (h : e ⊆ S) :
    liftEdge S (restrictEdge S e) = e := by
  ext x
  simp only [liftEdge, mem_image, mem_restrictEdge]
  constructor
  · rintro ⟨a, ha, rfl⟩; exact ha
  · intro hx; exact ⟨⟨x, h hx⟩, hx, rfl⟩

@[simp] theorem restrict_liftEdge (S : Finset V) (e : Finset ↥S) :
    restrictEdge S (liftEdge S e) = e := by
  ext x
  simp [liftEdge, Subtype.val_injective.eq_iff]

theorem liftEdge_injective (S : Finset V) : Function.Injective (liftEdge S) := by
  intro a b h
  simpa using congrArg (restrictEdge S) h

@[simp] theorem liftEdge_union (S : Finset V) (a b : Finset ↥S) :
    liftEdge S (a ∪ b) = liftEdge S a ∪ liftEdge S b := by exact image_union _ _

@[simp] theorem liftEdge_pair (S : Finset V) (a b : ↥S) :
    liftEdge S {a,b} = {a.val,b.val} := by simp [liftEdge]

@[simp] theorem liftEdge_card (S : Finset V) (a : Finset ↥S) :
    (liftEdge S a).card = a.card := card_image_of_injective _ Subtype.val_injective

@[simp] theorem liftEdge_disjoint (S : Finset V) (a b : Finset ↥S) :
    Disjoint (liftEdge S a) (liftEdge S b) ↔ Disjoint a b := by
  simp [liftEdge, disjoint_image, Subtype.val_injective.eq_iff]

@[expose] noncomputable def restrictedEdgeEquiv (S : Finset V) (E : Finset (Finset V))
    (h : ∀ e ∈ E, e ⊆ S) : ↥E ≃ ↥(restrictEdges S E) :=
  Equiv.ofBijective (fun e => ⟨restrictEdge S e.val, mem_image_of_mem _ e.property⟩) (by
    constructor
    · intro a b hab
      apply Subtype.ext
      have hh := congrArg (fun x : ↥(restrictEdges S E) => liftEdge S x.val) hab
      simpa [lift_restrictEdge, h a.val a.property, h b.val b.property] using hh
    · rintro ⟨b, hb⟩
      obtain ⟨a, ha, rfl⟩ := mem_image.mp hb
      exact ⟨⟨a,ha⟩,rfl⟩)

@[simp] theorem restrictedEdgeEquiv_val (S : Finset V) (E : Finset (Finset V))
    (h : ∀ e ∈ E, e ⊆ S) (e : ↥E) :
    (restrictedEdgeEquiv S E h e).val = restrictEdge S e.val := rfl

@[simp] theorem lift_restrictedEdgeEquiv_symm (S : Finset V) (E : Finset (Finset V))
    (h : ∀ e ∈ E, e ⊆ S) (e : ↥(restrictEdges S E)) :
    liftEdge S e.val = ((restrictedEdgeEquiv S E h).symm e).val := by
  obtain ⟨a, rfl⟩ := (restrictedEdgeEquiv S E h).surjective e
  simp [h a.val a.property]

namespace MixedCycleOnWitness
variable {r : ℕ} {S : Finset V} {markers edges : Finset (Finset V)}

@[expose] noncomputable def restrict (C : MixedCycleOnWitness r S markers edges) :
    MixedCycleWitness r (restrictEdges S markers) (restrictEdges S edges) := by
  let em := restrictedEdgeEquiv S markers (fun _ h => C.marked_subset_active h)
  let ee := restrictedEdgeEquiv S edges (fun _ h => C.edge_subset_active h)
  let j : Fin C.length → ↥S := fun i => ⟨C.junction i, C.junction_mem i⟩
  let P : ↥(restrictEdges S edges) → Finset ↥S :=
    fun e => restrictEdge S (C.privateBlock (ee.symm e))
  have hP (e) : liftEdge S (P e) = C.privateBlock (ee.symm e) :=
    lift_restrictEdge _ _ (C.private_subset_active _)
  have hJ : liftEdge S (univ.image j) = univ.image C.junction := by
    simp [liftEdge, image_image, j, Function.comp_def]
  refine {
    length := C.length
    length_ge := C.length_ge
    junction := j
    junction_injective := ?_
    junction_next_ne := ?_
    slot := C.slot.trans (Equiv.sumCongr em ee)
    privateBlock := P
    private_card := ?_
    private_disjoint := ?_
    junction_private_disjoint := ?_
    cover := ?_
    marked_matching := ?_
    slot_edge := ?_ }
  · intro a b h
    exact C.junction_injective (congrArg Subtype.val h)
  · intro i h
    exact C.junction_next_ne i (congrArg Subtype.val h)
  · intro e
    rw [← liftEdge_card S (P e), hP]
    exact C.private_card _
  · intro e f hef
    apply (liftEdge_disjoint S _ _).mp
    rw [hP, hP]
    exact C.private_disjoint (fun h => hef (ee.symm.injective h))
  · intro e
    apply (liftEdge_disjoint S _ _).mp
    rw [hJ, hP]
    exact C.junction_private_disjoint _
  · apply liftEdge_injective S
    rw [liftEdge_union, hJ]
    have hU : liftEdge S univ = S := by ext x; simp [liftEdge]
    rw [hU]
    apply C.cover.trans
    congr 1
    ext x
    simp only [liftEdge, mem_image, mem_biUnion, mem_univ, true_and]
    constructor
    · rintro ⟨e, he⟩
      refine ⟨⟨x, C.private_subset_active e he⟩, ⟨ee e, ?_⟩, rfl⟩
      simpa [P] using he
    · rintro ⟨v, ⟨e, he⟩, rfl⟩
      exact ⟨ee.symm e, by simpa [P] using he⟩
  · intro a ha b hb hab
    apply (liftEdge_disjoint S _ _).mp
    have hea := (em.symm ⟨a,ha⟩).property
    have heb := (em.symm ⟨b,hb⟩).property
    change Disjoint (liftEdge S a) (liftEdge S b)
    rw [lift_restrictedEdgeEquiv_symm S markers (fun _ h => C.marked_subset_active h) ⟨a,ha⟩,
      lift_restrictedEdgeEquiv_symm S markers (fun _ h => C.marked_subset_active h) ⟨b,hb⟩]
    exact C.marked_matching hea heb (by
      intro h
      apply hab
      have h' : em.symm ⟨a,ha⟩ = em.symm ⟨b,hb⟩ := Subtype.ext h
      exact congrArg Subtype.val (em.symm.injective h'))
  · intro i
    have hs := C.slot_edge i
    cases hi : C.slot i with
    | inl e =>
      simp only [Equiv.trans_apply, Equiv.sumCongr_apply, hi]
      apply liftEdge_injective S
      simp only [liftEdge_pair]
      rw [restrictedEdgeEquiv_val, lift_restrictEdge _ _ (C.marked_subset_active e.property)]
      simpa [j, hi] using hs
    | inr e =>
      simp only [Equiv.trans_apply, Equiv.sumCongr_apply, hi]
      apply liftEdge_injective S
      simp only [liftEdge_union, liftEdge_pair, hP, Equiv.symm_apply_apply]
      rw [restrictedEdgeEquiv_val, lift_restrictEdge _ _ (C.edge_subset_active e.property)]
      simpa [j, hi] using hs
end MixedCycleOnWitness

@[expose] noncomputable def liftedEdgeEquiv (S : Finset V) (E : Finset (Finset ↥S)) :
    ↥E ≃ ↥(E.image (liftEdge S)) :=
  Equiv.ofBijective (fun e => ⟨liftEdge S e.val, mem_image_of_mem _ e.property⟩) (by
    constructor
    · intro a b h
      exact Subtype.ext (liftEdge_injective S (congrArg Subtype.val h))
    · rintro ⟨e, he⟩
      obtain ⟨a, ha, rfl⟩ := mem_image.mp he
      exact ⟨⟨a,ha⟩,rfl⟩)

@[simp] theorem liftedEdgeEquiv_val (S : Finset V) (E : Finset (Finset ↥S)) (e : ↥E) :
    (liftedEdgeEquiv S E e).val = liftEdge S e.val := rfl

@[simp] theorem liftedEdgeEquiv_symm_val (S : Finset V) (E : Finset (Finset ↥S))
    (e : ↥(E.image (liftEdge S))) :
    liftEdge S ((liftedEdgeEquiv S E).symm e).val = e.val := by
  obtain ⟨a,rfl⟩ := (liftedEdgeEquiv S E).surjective e
  simp

namespace MixedCycleWitness
variable {r : ℕ} {S : Finset V} {markers edges : Finset (Finset ↥S)}

@[expose] noncomputable def lift (C : MixedCycleWitness r markers edges) :
    MixedCycleOnWitness r S (markers.image (liftEdge S)) (edges.image (liftEdge S)) := by
  let em := liftedEdgeEquiv S markers
  let ee := liftedEdgeEquiv S edges
  let j : Fin C.length → V := fun i => (C.junction i).val
  let P : ↥(edges.image (liftEdge S)) → Finset V :=
    fun e => liftEdge S (C.privateBlock (ee.symm e))
  have hJ : univ.image j = liftEdge S (univ.image C.junction) := by
    simp [liftEdge, image_image, j, Function.comp_def]
  refine {
    length := C.length
    length_ge := C.length_ge
    junction := j
    junction_injective := fun a b h => C.junction_injective (Subtype.ext h)
    junction_next_ne := fun i h => C.junction_next_ne i (Subtype.ext h)
    slot := C.slot.trans (Equiv.sumCongr em ee)
    privateBlock := P
    private_card := ?_
    private_disjoint := ?_
    junction_private_disjoint := ?_
    cover := ?_
    marked_matching := ?_
    slot_edge := ?_ }
  · intro e
    simpa [P] using C.private_card (ee.symm e)
  · intro e f hef
    exact (liftEdge_disjoint S _ _).mpr
      (C.private_disjoint (fun h => hef (ee.symm.injective h)))
  · intro e
    rw [hJ]
    exact (liftEdge_disjoint S _ _).mpr (C.junction_private_disjoint (ee.symm e))
  · have h := congrArg (liftEdge S) C.cover
    have hU : liftEdge S univ = S := by ext x; simp [liftEdge]
    rw [hU, liftEdge_union, ← hJ] at h
    apply h.trans
    congr 1
    ext x
    simp only [liftEdge, mem_image, mem_biUnion, mem_univ, true_and]
    constructor
    · rintro ⟨v, ⟨e, he⟩, rfl⟩
      exact ⟨ee e, by simpa [P, liftEdge] using
        (show ∃ v' ∈ C.privateBlock e, v'.val = v.val from ⟨v, he, rfl⟩)⟩
    · rintro ⟨e, he⟩
      obtain ⟨v, hv, rfl⟩ := mem_image.mp he
      exact ⟨v, ⟨ee.symm e, hv⟩, rfl⟩
  · intro a ha b hb hab
    obtain ⟨a', ha', rfl⟩ := mem_image.mp ha
    obtain ⟨b', hb', rfl⟩ := mem_image.mp hb
    exact (liftEdge_disjoint S _ _).mpr
      (C.marked_matching ha' hb' (fun h => hab (congrArg (liftEdge S) h)))
  · intro i
    have hs := C.slot_edge i
    cases hi : C.slot i with
    | inl e =>
      simp only [Equiv.trans_apply, Equiv.sumCongr_apply, hi, em, ee, liftedEdgeEquiv_val]
      rw [hi] at hs
      change e.val = _ at hs
      simpa [j] using congrArg (liftEdge S) hs
    | inr e =>
      simp only [Equiv.trans_apply, Equiv.sumCongr_apply, hi, em, ee, liftedEdgeEquiv_val]
      rw [hi] at hs
      change e.val = _ at hs
      have h := congrArg (liftEdge S) hs
      rw [liftEdge_union, liftEdge_pair] at h
      simpa [j, P, ee] using h
end MixedCycleWitness

/-- The active-set convention is exactly spanning on the corresponding subtype. -/
theorem isMixedCycleOn_iff_restrict {r : ℕ} {S : Finset V}
    {markers edges : Finset (Finset V)}
    (hM : ∀ e ∈ markers, e ⊆ S) (hE : ∀ e ∈ edges, e ⊆ S) :
    IsMixedCycleOn r S markers edges ↔
      IsMixedCycle r (restrictEdges S markers) (restrictEdges S edges) := by
  constructor
  · rintro ⟨C⟩
    exact ⟨C.restrict⟩
  · rintro ⟨C⟩
    have hm : (restrictEdges S markers).image (liftEdge S) = markers := by
      ext e
      simp only [restrictEdges, mem_image]
      constructor
      · rintro ⟨e', ⟨f,hf,rfl⟩, rfl⟩
        simpa [lift_restrictEdge S f (hM f hf)] using hf
      · intro he
        exact ⟨restrictEdge S e, ⟨e, he, rfl⟩, lift_restrictEdge S e (hM e he)⟩
    have he : (restrictEdges S edges).image (liftEdge S) = edges := by
      ext e
      simp only [restrictEdges, mem_image]
      constructor
      · rintro ⟨e', ⟨f,hf,rfl⟩, rfl⟩
        simpa [lift_restrictEdge S f (hE f hf)] using hf
      · intro he
        exact ⟨restrictEdge S e, ⟨e, he, rfl⟩, lift_restrictEdge S e (hE e he)⟩
    exact ⟨hm ▸ he ▸ C.lift⟩
end LooseHamilton
