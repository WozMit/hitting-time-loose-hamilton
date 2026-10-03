module

public import HittingTimeLooseHamilton.SourceMeanPositive
public import HittingTimeLooseHamilton.RootFreePrivateTests
public import HittingTimeLooseHamilton.RootFreeEndpointMean

public section

/-! Positivity of the exact normalizations used by the pre-registered tests,
derived from positive observed source counts and nesting of the actual hosts. -/
noncomputable section
namespace LooseHamilton
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A positive actual private source forces its outer source mean to be positive. -/
theorem privateRootSourceMean_pos_of_completionCount {r : ℕ}
    {M G H : Finset (Finset V)} {S q : Finset V} {x : V}
    (hr : 0 < r) (hGH : G ⊆ H)
    (hX : 0 < completionCount r M G (insert x S) q) :
    0 < privateRootSourceMean r H S x := by
  have h := inducedMean_pos_of_completionCount hr hGH hX
  simpa only [meanDegree, Fintype.card_coe, privateRootSourceMean] using h

/-- The source mean for either endpoint cut type is positive whenever its actual
root-free cut-core count is positive. Structural labels may be arbitrary. -/
theorem rootFreeEndpointMean_pos_of_source {r : ℕ}
    {M G H : Finset (Finset V)} {P : Finset V} {y z : V}
    (l : RootFreeEndpointLabel V) (hr : 0 < r) (hGH : G ⊆ H)
    (hX : 0 < rootFreeEndpointX r M G P y z l) :
    0 < rootFreeEndpointMean r H P y l := by
  have hroot : rootFreeEdges y G ⊆ H :=
    fun _ he => hGH (mem_filter.mp he).1
  cases l with
  | inl l => exact inducedMean_pos_of_cycleOnCount hr hroot hX
  | inr l => exact inducedMean_pos_of_cycleOnCount hr hroot hX

end LooseHamilton
