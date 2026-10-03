module

public import HittingTimeLooseHamilton.ActiveDirectedCompletions

public section

/-! Exact comparison with the existing directed count on the induced host. -/
noncomputable section
namespace LooseHamilton
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

@[expose] def directedCycleOnCount (r : ℕ) (S : Finset V) (markers host : Finset (Finset V))
    (root distinguished : ↥markers) (a y : V) : ℕ :=
  (directedCycleOnFamily r S markers host root distinguished a y).card

/-- Restriction of actual directed edge sets is a bijection. -/
@[expose] def directedCycleOnFamilyEquiv {r : ℕ} (hr : 3 ≤ r) (S : Finset V)
    (markers host : Finset (Finset V)) (hM : ∀ e ∈ markers, e ⊆ S)
    (root distinguished : ↥markers) (a : ↥root.val) (y : ↥S) :
    ↥(directedCycleOnFamily r S markers host root distinguished a.val y.val) ≃
      ↥(directedCycleFamily r (restrictEdges S markers) (inducedHost S host) ∅
        (activeRestrictedMarker S root) (activeRestrictedMarker S distinguished)
        (activeRestrictedRootPoint S hM root a) y) := by
  let f : ↥(directedCycleOnFamily r S markers host root distinguished a.val y.val) →
      ↥(directedCycleFamily r (restrictEdges S markers) (inducedHost S host) ∅
        (activeRestrictedMarker S root) (activeRestrictedMarker S distinguished)
        (activeRestrictedRootPoint S hM root a) y) := fun E =>
    ⟨restrictEdges S E.val, by
      obtain ⟨hE, hd⟩ := (mem_directedCycleOnFamily _ _ _ _ _ _ _ _ _).mp E.property
      apply (mem_directedCycleFamily _ _ _ _ _ _ _ _ _).mpr
      exact ⟨(cycleOnToRestricted hr S markers host ⟨E.val,hE⟩).property,
        rootedDirectedCycleOn_restrict hM root distinguished a y hd⟩⟩
  apply Equiv.ofBijective f
  constructor
  · intro E F h
    apply Subtype.ext
    have he := (mem_directedCycleOnFamily _ _ _ _ _ _ _ _ _).mp E.property
    have hf := (mem_directedCycleOnFamily _ _ _ _ _ _ _ _ _).mp F.property
    have hh : cycleOnToRestricted hr S markers host ⟨E.val,he.1⟩ =
        cycleOnToRestricted hr S markers host ⟨F.val,hf.1⟩ :=
      Subtype.ext (show restrictEdges S E.val = restrictEdges S F.val from congrArg (fun z => z.val) h)
    have hh' := cycleOnToRestricted_injective hr S markers host hh
    exact congrArg (fun z : ↥(cycleOnFamily r S markers host) => z.val) hh'
  · intro E
    obtain ⟨hE, hd⟩ := (mem_directedCycleFamily _ _ _ _ _ _ _ _ _).mp E.property
    let F := (cycleOnFamilyEquiv hr S markers host hM).symm ⟨E.val,hE⟩
    have hf : restrictEdges S F.val = E.val :=
      congrArg Subtype.val ((cycleOnFamilyEquiv hr S markers host hM).apply_symm_apply ⟨E.val,hE⟩)
    obtain ⟨C⟩ := ((mem_cycleOnFamily _ _ _ _ _).mp F.property).1
    have hdF : rootedDirectedCycleOn r S markers F.val root distinguished a.val y.val := by
      apply (rootedDirectedCycleOn_iff_restrict hM (fun _ he => C.edge_subset_active he)
        root distinguished a y).mpr
      rwa [hf]
    refine ⟨⟨F.val, (mem_directedCycleOnFamily _ _ _ _ _ _ _ _ _).mpr ⟨F.property,hdF⟩⟩, ?_⟩
    exact Subtype.ext hf

/-- No extra restriction from the changing marker ports is applied to the host. -/
theorem directedCycleOnCount_eq_directedCycleCount {r : ℕ} (hr : 3 ≤ r) (S : Finset V)
    (markers host : Finset (Finset V)) (hM : ∀ e ∈ markers, e ⊆ S)
    (root distinguished : ↥markers) (a : ↥root.val) (y : ↥S) :
    directedCycleOnCount r S markers host root distinguished a.val y.val =
      directedCycleCount r (restrictEdges S markers) (inducedHost S host) ∅
        (activeRestrictedMarker S root) (activeRestrictedMarker S distinguished)
        (activeRestrictedRootPoint S hM root a) y := by
  have h := Fintype.card_congr (directedCycleOnFamilyEquiv hr S markers host hM root distinguished a y)
  simpa only [directedCycleOnCount, directedCycleCount, Fintype.card_coe] using h

end LooseHamilton
