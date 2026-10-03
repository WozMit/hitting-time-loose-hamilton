module

public import HittingTimeLooseHamilton.BootstrapCatalogueGeometry
public import HittingTimeLooseHamilton.RootTestRegistry

public section

/-! # Fixed dummy tests for invalid raw labels
The only gate here is the explicit static geometry predicate. A dummy is rooted
at the ambient labelled vertex and declares every root edge bad. Construction
of the genuine eligible tests is deferred to item 33.10.
-/
noncomputable section
namespace LooseHamilton.BootstrapCatalogue
open Finset
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- No observations enter this fixed, empty-prescription, all-bad test. -/
@[expose] def dummy {r h : ℕ} {M : Finset (Finset V)} (i : Index r M) :
    RegisteredRootTest V r h where
  time := i.2.val
  root := root i.1
  prescribed := ∅
  prescribed_subset := empty_subset _
  prescribed_card := by simp
  badSet := fun _ => rootEdgeUniverse r (root i.1)
  bad_subset := fun _ => Subset.rfl

@[simp] theorem dummy_time {r h : ℕ} {M : Finset (Finset V)} (i : Index r M) :
    (dummy (h := h) i).time = i.2.val := rfl
@[simp] theorem dummy_root {r h : ℕ} {M : Finset (Finset V)} (i : Index r M) :
    (dummy (h := h) i).root = root i.1 := rfl
@[simp] theorem dummy_prescribed {r h : ℕ} {M : Finset (Finset V)} (i : Index r M) :
    (dummy (h := h) i).prescribed = ∅ := rfl
@[simp] theorem dummy_badSet {r h : ℕ} {M : Finset (Finset V)} (i : Index r M)
    (data : SimpleHypergraph V × SimpleHypergraph V) :
    (dummy (h := h) i).badSet data = rootEdgeUniverse r (root i.1) := rfl

/-- Every raw index remains registered; invalid static geometry gets the dummy.
This wrapper has no observed host, cut-presence or count-based gate. -/
@[expose] def withDummy {r h : ℕ} {M : Finset (Finset V)}
    (make : (i : Index r M) → admissible i.1 → RegisteredRootTest V r h)
    (i : Index r M) : RegisteredRootTest V r h :=
  if hi : admissible i.1 then make i hi else dummy i

theorem withDummy_valid {r h : ℕ} {M : Finset (Finset V)}
    (make : (i : Index r M) → admissible i.1 → RegisteredRootTest V r h)
    (i : Index r M) (hi : admissible i.1) : withDummy make i = make i hi := by
  simp [withDummy, hi]

theorem withDummy_invalid {r h : ℕ} {M : Finset (Finset V)}
    (make : (i : Index r M) → admissible i.1 → RegisteredRootTest V r h)
    (i : Index r M) (hi : ¬ admissible i.1) : withDummy make i = dummy i := by
  simp [withDummy, hi]

/-- Failed survival or source distinctness yields the same all-bad set for
all terminal/current observations. -/
theorem withDummy_invalid_badSet {r h : ℕ} {M : Finset (Finset V)}
    (make : (i : Index r M) → admissible i.1 → RegisteredRootTest V r h)
    (i : Index r M) (hi : ¬ admissible i.1)
    (data : SimpleHypergraph V × SimpleHypergraph V) :
    (withDummy make i).badSet data = rootEdgeUniverse r (root i.1) := by
  rw [withDummy_invalid make i hi]
  rfl

end LooseHamilton.BootstrapCatalogue
