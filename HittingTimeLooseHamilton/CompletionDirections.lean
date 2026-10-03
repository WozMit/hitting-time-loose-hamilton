module

public import HittingTimeLooseHamilton.CompletionModels
public import HittingTimeLooseHamilton.DirectedCompletions

public section

/-! # Directed private-block completion counts

The old root is retained when the fresh pair is added. `completionDirectedCount`
is the manuscript's `Y`, on the induced host after deleting the private block.
The endpoints and the root are transported to the actual surviving vertex type.
-/
noncomputable section
namespace LooseHamilton
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The old marked root survives in the enlarged, restricted marker family. -/
@[expose] def completionRestrictedRoot (markers : Finset (Finset V)) (P pair : Finset V)
    (root : ↥markers) : ↥(restrictEdges (univ \ P) (insert pair markers)) :=
  ⟨restrictEdge (univ \ P) root.val, mem_image_of_mem _ (mem_insert_of_mem root.property)⟩

/-- The newly inserted marker in the surviving vertex type. -/
@[expose] def completionRestrictedPair (markers : Finset (Finset V)) (P pair : Finset V) :
    ↥(restrictEdges (univ \ P) (insert pair markers)) :=
  ⟨restrictEdge (univ \ P) pair, mem_image_of_mem _ (mem_insert_self _ _)⟩

/-- Transport the prescribed initial root endpoint to the surviving type. -/
@[expose] def completionRestrictedRootPoint {r : ℕ} {markers : Finset (Finset V)}
    {P pair : Finset V} (h : LegalPrivateCompletion r markers P pair)
    (root : ↥markers) (a : ↥root.val) :
    ↥(completionRestrictedRoot markers P pair root).val :=
  ⟨⟨a.val, h.marker_subset_active root.property a.property⟩,
    (mem_restrictEdge _ _ _).mpr a.property⟩

/-- Transport an endpoint of the fresh pair to the surviving vertex type. -/
@[expose] def completionRestrictedEndpoint {r : ℕ} {markers : Finset (Finset V)}
    {P pair : Finset V} (h : LegalPrivateCompletion r markers P pair) (y : ↥pair) :
    ↥(univ \ P) :=
  ⟨y.val, h.pair_subset_active y.property⟩

/-- `Y_G(P;y→z)`: actual completions with the fresh pair starting at `y`,
relative to the fixed old root starting at `a`. -/
@[expose] def completionDirectedCount (r : ℕ) (markers host : Finset (Finset V))
    (P pair : Finset V) (h : LegalPrivateCompletion r markers P pair)
    (root : ↥markers) (a : ↥root.val) (y : ↥pair) : ℕ :=
  directedCycleCount r (restrictEdges (univ \ P) (insert pair markers))
    (inducedHost (univ \ P) host) ∅
    (completionRestrictedRoot markers P pair root)
    (completionRestrictedPair markers P pair)
    (completionRestrictedRootPoint h root a) (completionRestrictedEndpoint h y)

/-- The exact forward/reverse partition `W = Y_forward + Y_reverse`.
The two terms use the same prescribed direction of the old root. -/
theorem completionCount_split {r : ℕ} {markers host : Finset (Finset V)}
    {P pair : Finset V} (hr : 3 ≤ r) (h : LegalPrivateCompletion r markers P pair)
    (root : ↥markers) (a : ↥root.val) (y z : ↥pair)
    (hpair : pair = {y.val, z.val}) (hyz : y ≠ z) :
    completionCount r markers host P pair =
      completionDirectedCount r markers host P pair h root a y +
        completionDirectedCount r markers host P pair h root a z := by
  rw [completionCount_eq_X hr h]
  have hp : (completionRestrictedPair markers P pair).val =
      {completionRestrictedEndpoint h y, completionRestrictedEndpoint h z} := by
    ext x
    simp only [completionRestrictedPair, mem_restrictEdge, hpair,
      mem_insert, mem_singleton]
    simp only [Subtype.ext_iff, completionRestrictedEndpoint]
  have hn : completionRestrictedEndpoint h y ≠ completionRestrictedEndpoint h z := by
    intro he
    apply hyz
    exact Subtype.ext (congrArg (fun x : ↥(univ \ P) => x.val) he)
  exact directedCycleCount_split hr ∅
    (completionRestrictedRoot markers P pair root)
    (completionRestrictedPair markers P pair)
    (completionRestrictedRootPoint h root a) hp hn

/-- The same identity in the manuscript's endpoint notation. -/
theorem completionCount_split_endpoints {r : ℕ} {markers host : Finset (Finset V)}
    {P : Finset V} (hr : 3 ≤ r) (y z : V) (hyz : y ≠ z)
    (h : LegalPrivateCompletion r markers P {y, z})
    (root : ↥markers) (a : ↥root.val) :
    completionCount r markers host P {y, z} =
      completionDirectedCount r markers host P {y, z} h root a ⟨y, by simp⟩ +
        completionDirectedCount r markers host P {y, z} h root a ⟨z, by simp⟩ := by
  apply completionCount_split hr h root a _ _ rfl
  intro he
  exact hyz (congrArg Subtype.val he)

end LooseHamilton
