module

public import HittingTimeLooseHamilton.BootstrapNestedRestriction
public import HittingTimeLooseHamilton.AuxiliaryFrameParameters

public section

/-! Forget frame directions and restrict actual edge families to a containing
base. Injectivity uses the cached lifting inverse, not direction retention. -/
noncomputable section
namespace LooseHamilton.AuxiliaryFrame.Frame
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {r : ℕ} {M : Finset (Finset V)}

@[expose] def completionForgetDirections (F : Frame r M) (H : SimpleHypergraph V)
    (c : Finset V × V × V) :
    ↥(F.completionFamily H c) →
      ↥(cycleOnFamily r (F.active \ c.1) (insert {c.2.1,c.2.2} F.markers)
        (H ∩ allowedEdges r (originalPorts M))) := fun E => ⟨E.val, by
  obtain ⟨hhost,C,_,_⟩ := (F.mem_completionFamily H c E.val).mp E.property
  exact (mem_cycleOnFamily _ _ _ _ _).mpr
    ⟨⟨C⟩, fun e he => (mem_filter.mp (hhost he)).1⟩⟩

theorem completionForgetDirections_injective (F : Frame r M) (H : SimpleHypergraph V)
    (c : Finset V × V × V) :
    Function.Injective (F.completionForgetDirections H c) := by
  intro E E' h
  have hh := congrArg Subtype.val h
  exact Subtype.ext hh

@[expose] def completionRestrict (F : Frame r M) (H : SimpleHypergraph V)
    (c : Finset V × V × V) (B : Finset V) (hB : F.active ⊆ B) :
    ↥(F.completionFamily H c) →
      ↥(cycleOnFamily r (restrictEdge B (F.active \ c.1))
        (restrictEdges B (insert {c.2.1,c.2.2} F.markers))
        (inducedHost B (H ∩ allowedEdges r (originalPorts M)))) :=
  cycleOnWithinToRestricted r (F.active \ c.1) B (sdiff_subset.trans hB) _ _ ∘
    F.completionForgetDirections H c

theorem completionRestrict_injective (F : Frame r M) (H : SimpleHypergraph V)
    (c : Finset V × V × V) (B : Finset V) (hB : F.active ⊆ B) :
    Function.Injective (F.completionRestrict H c B hB) :=
  (cycleOnWithinToRestricted_injective r (F.active \ c.1) B
    (sdiff_subset.trans hB) _ _).comp (F.completionForgetDirections_injective H c)

theorem completionCount_le_restricted (F : Frame r M) (H : SimpleHypergraph V)
    (c : Finset V × V × V) (B : Finset V) (hB : F.active ⊆ B) :
    F.completionCount H c ≤
      cycleOnCount r (restrictEdge B (F.active \ c.1))
        (restrictEdges B (insert {c.2.1,c.2.2} F.markers))
        (inducedHost B (H ∩ allowedEdges r (originalPorts M))) := by
  simpa only [completionCount, cycleOnCount, Fintype.card_coe] using
    Fintype.card_le_of_injective _ (F.completionRestrict_injective H c B hB)

end LooseHamilton.AuxiliaryFrame.Frame
