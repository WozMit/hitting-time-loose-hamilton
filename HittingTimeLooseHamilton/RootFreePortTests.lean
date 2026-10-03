module

public import HittingTimeLooseHamilton.RootFreeCountInvariance
public import HittingTimeLooseHamilton.CompletionModels
public import HittingTimeLooseHamilton.RootSamplingModels

public section

/-! Original-port tests on the actual vertex set with the old port deleted.
The old marker is removed but ordinary-edge prohibition still uses the fixed
original port set `U`. -/
noncomputable section
namespace LooseHamilton
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Completion in `G-y₀`, after removing its original marker. The deleted root
is removed from the active vertex set, not merely isolated in the host. -/
@[expose] def rootFreePortCompletion (r : ℕ) (M G : Finset (Finset V))
    (y₀ z₀ : V) (P pair : Finset V) : ℕ :=
  cycleOnCount r ((univ.erase y₀) \ P) (insert pair (M.erase {y₀,z₀}))
    (rootFreeEdges y₀ G)

/-- The source `Z=W_F(P;uz₀)`, for fixed labels `P,u` registered in advance. -/
@[expose] def rootFreePortSource (r : ℕ) (M G : Finset (Finset V))
    (y₀ z₀ : V) (P : Finset V) (u : V) : ℕ :=
  rootFreePortCompletion r M G y₀ z₀ P {u,z₀}

/-- The sum in equation (portbad), with all choices of the other junction. -/
@[expose] def rootFreePortScore (r : ℕ) (M G : Finset (Finset V))
    (y₀ z₀ : V) (A : Finset V) : ℕ :=
  ∑ v ∈ A, rootFreePortCompletion r M G y₀ z₀ (A.erase v) {v,z₀}

/-- Forbidden and colliding labels are bad as well as those with small total
completion count. Each link is represented by its full root edge. -/
@[expose] def rootFreePortBadSet (r : ℕ) (M G : Finset (Finset V))
    (U P : Finset V) (y₀ z₀ u : V) (c : ℝ) : Finset (Finset V) := by
  classical
  exact (rootEdgeUniverse r y₀).filter (fun e =>
    e ∉ allowedEdges r U ∨
    (¬ ∀ v ∈ e.erase y₀,
      LegalPrivateCompletion r (M.erase {y₀,z₀}) ((e.erase y₀).erase v) {v,z₀}) ∨
    (rootFreePortScore r M G y₀ z₀ (e.erase y₀) : ℝ) <
      c * rootFreePortSource r M G y₀ z₀ P u)

/-- Counts and their source normalization are fixed by the deleted-root host. -/
theorem rootFreePortCompletion_congr (r : ℕ) (M G H : Finset (Finset V))
    (y₀ z₀ : V) (P pair : Finset V)
    (h : rootFreeEdges y₀ G = rootFreeEdges y₀ H) :
    rootFreePortCompletion r M G y₀ z₀ P pair =
      rootFreePortCompletion r M H y₀ z₀ P pair := by
  simp only [rootFreePortCompletion, h]

/-- Fiberwise measurability of the original-port link test. -/
theorem rootFreePortBadSet_congr (r : ℕ) (M G H : Finset (Finset V))
    (U P : Finset V) (y₀ z₀ u : V) (c : ℝ)
    (h : rootFreeEdges y₀ G = rootFreeEdges y₀ H) :
    rootFreePortBadSet r M G U P y₀ z₀ u c =
      rootFreePortBadSet r M H U P y₀ z₀ u c := by
  classical
  unfold rootFreePortBadSet
  apply filter_congr
  intro e _
  simp only [rootFreePortScore, rootFreePortSource, rootFreePortCompletion, h]

/-- Root-free evaluation is the actual count on the deleted-root vertex set. -/
theorem rootFreePortCompletion_eq (r : ℕ) (M G : Finset (Finset V))
    (y₀ z₀ : V) (P pair : Finset V) :
    rootFreePortCompletion r M G y₀ z₀ P pair =
      cycleOnCount r ((univ.erase y₀) \ P) (insert pair (M.erase {y₀,z₀})) G := by
  unfold rootFreePortCompletion
  exact cycleOnCount_rootFreeEdges r _ _ G y₀ (by simp)

/-- A good original-port edge has legal labels and the required sum of actual
completions, with the removed marker and deleted root represented explicitly. -/
theorem rootFreePort_good_score (r : ℕ) (M G : Finset (Finset V))
    (U P : Finset V) (y₀ z₀ u : V) (c : ℝ) (e : Finset V)
    (he : e ∈ rootEdgeUniverse r y₀)
    (hgood : e ∉ rootFreePortBadSet r M G U P y₀ z₀ u c) :
    e ∈ allowedEdges r U ∧
    (∀ v ∈ e.erase y₀,
      LegalPrivateCompletion r (M.erase {y₀,z₀}) ((e.erase y₀).erase v) {v,z₀}) ∧
    c * rootFreePortSource r M G y₀ z₀ P u ≤
      (rootFreePortScore r M G y₀ z₀ (e.erase y₀) : ℝ) := by
  classical
  simpa only [rootFreePortBadSet, mem_filter, he, true_and, not_or, not_not, not_lt] using hgood

end LooseHamilton
