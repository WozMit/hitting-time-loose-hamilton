module

public import HittingTimeLooseHamilton.CycleOnCounting

public section

noncomputable section
namespace LooseHamilton
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace MixedCycleOnWitness
variable {r : ℕ} {S : Finset V} {markers edges : Finset (Finset V)}
@[expose] noncomputable def restrictWithin (C : MixedCycleOnWitness r S markers edges)
    (A : Finset V) (hSA : S ⊆ A) :
    MixedCycleOnWitness r (restrictEdge A S) (restrictEdges A markers) (restrictEdges A edges) := by
  let em := restrictedEdgeEquiv A markers (fun _ h => (C.marked_subset_active h).trans hSA)
  let ee := restrictedEdgeEquiv A edges (fun _ h => (C.edge_subset_active h).trans hSA)
  let j : Fin C.length → ↥A := fun i => ⟨C.junction i, hSA (C.junction_mem i)⟩
  let P : ↥(restrictEdges A edges) → Finset ↥A :=
    fun e => restrictEdge A (C.privateBlock (ee.symm e))
  have hP (e) : liftEdge A (P e) = C.privateBlock (ee.symm e) :=
    lift_restrictEdge _ _ ((C.private_subset_active _).trans hSA)
  have hJ : liftEdge A (univ.image j) = univ.image C.junction := by
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
    rw [← liftEdge_card A (P e), hP]
    exact C.private_card _
  · intro e f hef
    apply (liftEdge_disjoint A _ _).mp
    rw [hP, hP]
    exact C.private_disjoint (fun h => hef (ee.symm.injective h))
  · intro e
    apply (liftEdge_disjoint A _ _).mp
    rw [hJ, hP]
    exact C.junction_private_disjoint _
  · apply liftEdge_injective A
    rw [liftEdge_union, hJ]
    have hU : liftEdge A (restrictEdge A S) = S := lift_restrictEdge A S hSA
    rw [hU]
    apply C.cover.trans
    congr 1
    ext x
    simp only [liftEdge, mem_image, mem_biUnion, mem_univ, true_and]
    constructor
    · rintro ⟨e, he⟩
      refine ⟨⟨x, hSA (C.private_subset_active e he)⟩, ⟨ee e, ?_⟩, rfl⟩
      simpa [P] using he
    · rintro ⟨v, ⟨e, he⟩, rfl⟩
      exact ⟨ee.symm e, by simpa [P] using he⟩
  · intro a ha b hb hab
    apply (liftEdge_disjoint A _ _).mp
    have hea := (em.symm ⟨a,ha⟩).property
    have heb := (em.symm ⟨b,hb⟩).property
    change Disjoint (liftEdge A a) (liftEdge A b)
    rw [lift_restrictedEdgeEquiv_symm A markers (fun _ h => (C.marked_subset_active h).trans hSA) ⟨a,ha⟩,
      lift_restrictedEdgeEquiv_symm A markers (fun _ h => (C.marked_subset_active h).trans hSA) ⟨b,hb⟩]
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
      apply liftEdge_injective A
      simp only [liftEdge_pair]
      rw [restrictedEdgeEquiv_val, lift_restrictEdge _ _ ((C.marked_subset_active e.property).trans hSA)]
      simpa [j, hi] using hs
    | inr e =>
      simp only [Equiv.trans_apply, Equiv.sumCongr_apply, hi]
      apply liftEdge_injective A
      simp only [liftEdge_union, liftEdge_pair, hP, Equiv.symm_apply_apply]
      rw [restrictedEdgeEquiv_val, lift_restrictEdge _ _ ((C.edge_subset_active e.property).trans hSA)]
      simpa [j, hi] using hs
end MixedCycleOnWitness
namespace MixedCycleOnWitness
variable {r : ℕ} {S : Finset V} {markers edges : Finset (Finset ↥S)}
@[expose] noncomputable def liftWithin {T : Finset ↥S} (C : MixedCycleOnWitness r T markers edges) :
    MixedCycleOnWitness r (liftEdge S T) (markers.image (liftEdge S)) (edges.image (liftEdge S)) := by
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
    rw [liftEdge_union, ← hJ] at h
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
end MixedCycleOnWitness

/-- Restriction to a containing base preserves the actual cycle family. -/
@[expose] def cycleOnWithinToRestricted (r : ℕ) (S A : Finset V) (hSA : S ⊆ A)
    (markers host : Finset (Finset V)) :
    ↥(cycleOnFamily r S markers host) →
      ↥(cycleOnFamily r (restrictEdge A S) (restrictEdges A markers) (inducedHost A host)) :=
  fun E => ⟨restrictEdges A E.val, by
    obtain ⟨⟨C⟩,hE⟩ := (mem_cycleOnFamily _ _ _ _ _).mp E.property
    exact (mem_cycleOnFamily _ _ _ _ _).mpr ⟨⟨C.restrictWithin A hSA⟩,
      restrictEdges_subset_inducedHost A _ _
        (fun e he => (C.edge_subset_active he).trans hSA) hE⟩⟩

theorem cycleOnWithinToRestricted_injective (r : ℕ) (S A : Finset V) (hSA : S ⊆ A)
    (markers host : Finset (Finset V)) :
    Function.Injective (cycleOnWithinToRestricted r S A hSA markers host) := by
  intro E F h
  apply Subtype.ext
  obtain ⟨C⟩ := ((mem_cycleOnFamily _ _ _ _ _).mp E.property).1
  obtain ⟨D⟩ := ((mem_cycleOnFamily _ _ _ _ _).mp F.property).1
  have he : restrictEdges A E.val = restrictEdges A F.val := congrArg Subtype.val h
  have hh := congrArg (fun K => K.image (liftEdge A)) he
  simpa only [liftEdges_restrictEdges A E.val
      (fun e he => (C.edge_subset_active he).trans hSA),
    liftEdges_restrictEdges A F.val
      (fun e he => (D.edge_subset_active he).trans hSA)] using hh

/-- Ambient and base-subtype edge families are in bijection before further deletion. -/
@[expose] def cycleOnWithinFamilyEquiv (r : ℕ) (S A : Finset V) (hSA : S ⊆ A)
    (markers host : Finset (Finset V)) (hM : ∀ e ∈ markers, e ⊆ A) :
    ↥(cycleOnFamily r S markers host) ≃
      ↥(cycleOnFamily r (restrictEdge A S) (restrictEdges A markers) (inducedHost A host)) :=
  Equiv.ofBijective (cycleOnWithinToRestricted r S A hSA markers host) ⟨
    cycleOnWithinToRestricted_injective r S A hSA markers host, by
      intro E
      obtain ⟨⟨C⟩,hE⟩ := (mem_cycleOnFamily _ _ _ _ _).mp E.property
      have hc : IsMixedCycleOn r S markers (E.val.image (liftEdge A)) := by
        have hh := C.liftWithin
        rw [lift_restrictEdge A S hSA, liftEdges_restrictEdges A markers hM] at hh
        exact ⟨hh⟩
      refine ⟨⟨E.val.image (liftEdge A),
        (mem_cycleOnFamily _ _ _ _ _).mpr ⟨hc,liftEdges_subset_host A E.val host hE⟩⟩,?_⟩
      exact Subtype.ext (restrictEdges_liftEdges A E.val)⟩

/-- Exact count transport into a base containing the active vertices. -/
theorem cycleOnCount_restrictWithin (r : ℕ) (S A : Finset V) (hSA : S ⊆ A)
    (markers host : Finset (Finset V)) (hM : ∀ e ∈ markers, e ⊆ A) :
    cycleOnCount r S markers host =
      cycleOnCount r (restrictEdge A S) (restrictEdges A markers) (inducedHost A host) := by
  have h := Fintype.card_congr (cycleOnWithinFamilyEquiv r S A hSA markers host hM)
  simpa only [Fintype.card_coe, cycleOnCount] using h

end LooseHamilton
