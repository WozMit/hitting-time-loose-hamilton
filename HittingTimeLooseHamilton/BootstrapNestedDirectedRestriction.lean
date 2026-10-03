module

public import HittingTimeLooseHamilton.BootstrapNestedRestriction
public import HittingTimeLooseHamilton.ActiveDirectedCounting

public section

/-! Restricting first to an original base preserves both prescribed directions. -/
noncomputable section
namespace LooseHamilton
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

namespace MixedCycleOnWitness
@[simp] theorem restrictWithin_marker_start {r : ℕ} {S : Finset V}
    {M E : Finset (Finset V)} (C : MixedCycleOnWitness r S M E)
    (A : Finset V) (hSA : S ⊆ A) (m : ↥M) :
    ((C.restrictWithin A hSA).junction
      ((C.restrictWithin A hSA).slot.symm (.inl (activeRestrictedMarker A m)))).val =
      C.junction (C.slot.symm (.inl m)) := by
  have hs : (C.restrictWithin A hSA).slot.symm (.inl (activeRestrictedMarker A m)) =
      C.slot.symm (.inl m) := by
    apply (C.restrictWithin A hSA).slot.injective
    rw [Equiv.apply_symm_apply]
    change _ = (Equiv.sumCongr
      (restrictedEdgeEquiv A M (fun _ h => (C.marked_subset_active h).trans hSA))
      (restrictedEdgeEquiv A E (fun _ h => (C.edge_subset_active h).trans hSA)))
      (C.slot (C.slot.symm (.inl m)))
    rw [Equiv.apply_symm_apply]
    rfl
  change C.junction ((C.restrictWithin A hSA).slot.symm (.inl (activeRestrictedMarker A m))) = _
  rw [hs]

@[simp] theorem liftWithin_marker_start {r : ℕ} {A : Finset V} {S : Finset ↥A}
    {M E : Finset (Finset ↥A)} (C : MixedCycleOnWitness r S M E) (m : ↥M) :
    C.liftWithin.junction (C.liftWithin.slot.symm (.inl (liftedEdgeEquiv A M m))) =
      (C.junction (C.slot.symm (.inl m))).val := by
  have hs : C.liftWithin.slot.symm (.inl (liftedEdgeEquiv A M m)) =
      C.slot.symm (.inl m) := by
    apply C.liftWithin.slot.injective
    rw [Equiv.apply_symm_apply]
    change _ = (Equiv.sumCongr (liftedEdgeEquiv A M) (liftedEdgeEquiv A E))
      (C.slot (C.slot.symm (.inl m)))
    rw [Equiv.apply_symm_apply]
    rfl
  change (C.junction (C.liftWithin.slot.symm (.inl (liftedEdgeEquiv A M m)))).val = _
  rw [hs]
end MixedCycleOnWitness

theorem rootedDirectedCycleOn_iff_restrictWithin {r : ℕ} {A S : Finset V}
    (hSA : S ⊆ A) {M E : Finset (Finset V)}
    (hM : ∀ e ∈ M, e ⊆ A) (hE : ∀ e ∈ E, e ⊆ A)
    (p q : ↥M) (a y : ↥A) :
    rootedDirectedCycleOn r S M E p q a.val y.val ↔
      rootedDirectedCycleOn r (restrictEdge A S) (restrictEdges A M) (restrictEdges A E)
        (activeRestrictedMarker A p) (activeRestrictedMarker A q) a y := by
  constructor
  · rintro ⟨C,hp,hq⟩
    refine ⟨C.restrictWithin A hSA,Subtype.ext ?_,Subtype.ext ?_⟩
    · simpa only [MixedCycleOnWitness.restrictWithin_marker_start] using hp
    · simpa only [MixedCycleOnWitness.restrictWithin_marker_start] using hq
  · rintro ⟨C,hp,hq⟩
    have hl : rootedDirectedCycleOn r (liftEdge A (restrictEdge A S))
        ((restrictEdges A M).image (liftEdge A)) ((restrictEdges A E).image (liftEdge A))
        (liftedEdgeEquiv A _ (activeRestrictedMarker A p))
        (liftedEdgeEquiv A _ (activeRestrictedMarker A q)) a.val y.val := by
      refine ⟨C.liftWithin,?_,?_⟩
      · simpa only [MixedCycleOnWitness.liftWithin_marker_start] using congrArg Subtype.val hp
      · simpa only [MixedCycleOnWitness.liftWithin_marker_start] using congrArg Subtype.val hq
    rw [lift_restrictEdge A S hSA] at hl
    apply (rootedDirectedCycleOn_congr (liftEdges_restrictEdges A M hM)
      (liftEdges_restrictEdges A E hE) _ _ p q ?_ ?_ a.val y.val).mp hl
    · exact lift_restrictEdge A p.val (hM _ p.property)
    · exact lift_restrictEdge A q.val (hM _ q.property)

/-- Actual directed edge sets, with both starts retained, are in bijection under
restriction to any larger base than their active set. -/
@[expose] def directedCycleOnFamilyEquiv_restrictWithin {r : ℕ} (A S : Finset V)
    (hSA : S ⊆ A) (M H : Finset (Finset V)) (hM : ∀ e ∈ M, e ⊆ S)
    (p q : ↥M) (a y : ↥A) :
    ↥(directedCycleOnFamily r S M H p q a.val y.val) ≃
      ↥(directedCycleOnFamily r (restrictEdge A S) (restrictEdges A M) (inducedHost A H)
        (activeRestrictedMarker A p) (activeRestrictedMarker A q) a y) := by
  let f : ↥(directedCycleOnFamily r S M H p q a.val y.val) →
      ↥(directedCycleOnFamily r (restrictEdge A S) (restrictEdges A M) (inducedHost A H)
        (activeRestrictedMarker A p) (activeRestrictedMarker A q) a y) := fun E =>
    ⟨restrictEdges A E.val, by
      obtain ⟨hE,hd⟩ := (mem_directedCycleOnFamily _ _ _ _ _ _ _ _ _).mp E.property
      obtain ⟨⟨C⟩,hEH⟩ := (mem_cycleOnFamily _ _ _ _ _).mp hE
      apply (mem_directedCycleOnFamily _ _ _ _ _ _ _ _ _).mpr
      refine ⟨(mem_cycleOnFamily _ _ _ _ _).mpr ⟨⟨C.restrictWithin A hSA⟩,?_⟩,?_⟩
      · exact restrictEdges_subset_inducedHost A _ _
          (fun e he => (C.edge_subset_active he).trans hSA) hEH
      · exact (rootedDirectedCycleOn_iff_restrictWithin hSA
          (fun e he => (hM e he).trans hSA)
          (fun e he => (C.edge_subset_active he).trans hSA) p q a y).mp hd⟩
  apply Equiv.ofBijective f
  constructor
  · intro E F heq
    have hE := (mem_directedCycleOnFamily _ _ _ _ _ _ _ _ _).mp E.property
    have hF := (mem_directedCycleOnFamily _ _ _ _ _ _ _ _ _).mp F.property
    obtain ⟨CE⟩ := ((mem_cycleOnFamily _ _ _ _ _).mp hE.1).1
    obtain ⟨CF⟩ := ((mem_cycleOnFamily _ _ _ _ _).mp hF.1).1
    have he : restrictEdges A E.val = restrictEdges A F.val := congrArg Subtype.val heq
    have hl := congrArg (fun K => K.image (liftEdge A)) he
    apply Subtype.ext
    simpa only [liftEdges_restrictEdges A E.val
      (fun e he => (CE.edge_subset_active he).trans hSA),
      liftEdges_restrictEdges A F.val
      (fun e he => (CF.edge_subset_active he).trans hSA)] using hl
  · intro E
    obtain ⟨hE,hd⟩ := (mem_directedCycleOnFamily _ _ _ _ _ _ _ _ _).mp E.property
    have hEH := ((mem_cycleOnFamily _ _ _ _ _).mp hE).2
    let K := E.val.image (liftEdge A)
    have hKA : ∀ e ∈ K, e ⊆ A := by
      intro e he
      obtain ⟨f,hf,rfl⟩ := mem_image.mp he
      exact liftEdge_subset A f
    have hK : rootedDirectedCycleOn r S M K p q a.val y.val := by
      apply (rootedDirectedCycleOn_iff_restrictWithin hSA
        (fun e he => (hM e he).trans hSA) hKA p q a y).mpr
      simpa only [K,restrictEdges_liftEdges] using hd
    have hmem : K ∈ directedCycleOnFamily r S M H p q a.val y.val := by
      apply (mem_directedCycleOnFamily _ _ _ _ _ _ _ _ _).mpr
      exact ⟨(mem_cycleOnFamily _ _ _ _ _).mpr ⟨⟨hK.choose⟩,liftEdges_subset_host A _ _ hEH⟩,hK⟩
    refine ⟨⟨K,hmem⟩,?_⟩
    apply Subtype.ext
    exact restrictEdges_liftEdges A E.val

theorem directedCycleOnCount_restrictWithin {r : ℕ} (A S : Finset V)
    (hSA : S ⊆ A) (M H : Finset (Finset V)) (hM : ∀ e ∈ M, e ⊆ S)
    (p q : ↥M) (a y : ↥A) :
    directedCycleOnCount r S M H p q a.val y.val =
      directedCycleOnCount r (restrictEdge A S) (restrictEdges A M) (inducedHost A H)
        (activeRestrictedMarker A p) (activeRestrictedMarker A q) a y := by
  have h := Fintype.card_congr
    (directedCycleOnFamilyEquiv_restrictWithin (r := r) A S hSA M H hM p q a y)
  simpa only [directedCycleOnCount, Fintype.card_coe] using h

end LooseHamilton
