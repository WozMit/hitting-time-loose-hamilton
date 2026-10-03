module

public import HittingTimeLooseHamilton.RootLinkModels
public import HittingTimeLooseHamilton.ActiveDirectedCounting
public import HittingTimeLooseHamilton.CompletionModels

public section

/-! Removing the root link leaves every count on an active set avoiding the
root unchanged. These are host equalities, not merely finite measurability. -/
noncomputable section
namespace LooseHamilton
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

@[simp] theorem rootFreeEdges_idempotent (x : V) (host : Finset (Finset V)) :
    rootFreeEdges x (rootFreeEdges x host) = rootFreeEdges x host := by
  ext e
  simp [rootFreeEdges]

/-- A surviving induced host ignores all root-incident edges. -/
theorem inducedHost_rootFreeEdges (S : Finset V) (host : Finset (Finset V))
    (x : V) (hx : x ∉ S) :
    inducedHost S (rootFreeEdges x host) = inducedHost S host := by
  ext e
  have hxe : x ∉ ambientEdge S e := by
    intro h
    exact hx (liftEdge_subset S e (by simpa using h))
  simp only [mem_inducedHost, rootFreeEdges, mem_filter]
  exact and_iff_left hxe

theorem cycleOnFamily_rootFreeEdges (r : ℕ) (S : Finset V)
    (markers host : Finset (Finset V)) (x : V) (hx : x ∉ S) :
    cycleOnFamily r S markers (rootFreeEdges x host) =
      cycleOnFamily r S markers host :=
  cycleOnFamily_congr_inducedHost r S markers _ _ (inducedHost_rootFreeEdges S host x hx)

theorem cycleOnCount_rootFreeEdges (r : ℕ) (S : Finset V)
    (markers host : Finset (Finset V)) (x : V) (hx : x ∉ S) :
    cycleOnCount r S markers (rootFreeEdges x host) =
      cycleOnCount r S markers host :=
  congrArg card (cycleOnFamily_rootFreeEdges r S markers host x hx)

theorem directedCycleOnFamily_rootFreeEdges (r : ℕ) (S : Finset V)
    (markers host : Finset (Finset V)) (root distinguished : ↥markers) (a y x : V)
    (hx : x ∉ S) :
    directedCycleOnFamily r S markers (rootFreeEdges x host) root distinguished a y =
      directedCycleOnFamily r S markers host root distinguished a y := by
  unfold directedCycleOnFamily
  rw [cycleOnFamily_rootFreeEdges r S markers host x hx]

theorem directedCycleOnCount_rootFreeEdges (r : ℕ) (S : Finset V)
    (markers host : Finset (Finset V)) (root distinguished : ↥markers) (a y x : V)
    (hx : x ∉ S) :
    directedCycleOnCount r S markers (rootFreeEdges x host) root distinguished a y =
      directedCycleOnCount r S markers host root distinguished a y :=
  congrArg card (directedCycleOnFamily_rootFreeEdges r S markers host root distinguished a y x hx)

/-- A completion deleting its root is determined by the root-free host. -/
theorem completionCount_rootFreeEdges (r : ℕ) (markers host : Finset (Finset V))
    (P q : Finset V) (x : V) (hx : x ∈ P) :
    completionCount r markers (rootFreeEdges x host) P q =
      completionCount r markers host P q := by
  exact cycleOnCount_rootFreeEdges r (univ \ P) (insert q markers) host x (by simp [hx])

end LooseHamilton
