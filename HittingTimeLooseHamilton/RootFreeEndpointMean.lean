module

public import HittingTimeLooseHamilton.RootFreeEndpointTests

public section

/-! The endpoint scale uses the mean degree of the outer host on the surviving
cut vertices. This parameter is root-free along with the actual cycle counts. -/
noncomputable section
namespace LooseHamilton
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

@[expose] def rootFreeEndpointActive (P : Finset V) (y : V) : RootFreeEndpointLabel V → Finset V
  | .inl l => univ \ (P ∪ l.deleted y)
  | .inr l => univ \ (P ∪ l.deleted y)

theorem root_not_mem_endpointActive (P : Finset V) (y : V) (l : RootFreeEndpointLabel V) :
    y ∉ rootFreeEndpointActive P y l := by
  cases l <;> simp [rootFreeEndpointActive, EndpointCutLabelI.deleted, EndpointCutLabelII.deleted]

/-- Actual surviving outer-host mean, with no assumed root-free parameter. -/
@[expose] def rootFreeEndpointMean (r : ℕ) (outer : Finset (Finset V)) (P : Finset V)
    (y : V) (l : RootFreeEndpointLabel V) : ℝ :=
  meanDegree (V := ↥(rootFreeEndpointActive P y l)) r
    (inducedHost (rootFreeEndpointActive P y l) outer).card

theorem rootFreeEndpointMean_rootFree (r : ℕ) (outer : Finset (Finset V)) (P : Finset V)
    (y : V) (l : RootFreeEndpointLabel V) :
    rootFreeEndpointMean r (rootFreeEdges y outer) P y l = rootFreeEndpointMean r outer P y l := by
  unfold rootFreeEndpointMean
  rw [inducedHost_rootFreeEdges _ outer y (root_not_mem_endpointActive P y l)]

theorem rootFreeEndpointMean_congr (r : ℕ) (outer outer' : Finset (Finset V))
    (P : Finset V) (y : V) (l : RootFreeEndpointLabel V)
    (h : rootFreeEdges y outer = rootFreeEdges y outer') :
    rootFreeEndpointMean r outer P y l = rootFreeEndpointMean r outer' P y l := by
  rw [← rootFreeEndpointMean_rootFree r outer, ← rootFreeEndpointMean_rootFree r outer', h]

/-- Full endpoint test, with its actual outer-host normalization, is constant
on each root-free terminal/current observation fiber. -/
theorem rootFreeEndpointBadSet_mean_congr (r : ℕ) (M G G' outer outer' : Finset (Finset V))
    (P U : Finset V) (y z t : V) (l : RootFreeEndpointLabel V) (c : ℝ)
    (hG : rootFreeEdges y G = rootFreeEdges y G')
    (houter : rootFreeEdges y outer = rootFreeEdges y outer') :
    rootFreeEndpointBadSet r M G P U y z t l c (rootFreeEndpointMean r outer P y l) =
      rootFreeEndpointBadSet r M G' P U y z t l c (rootFreeEndpointMean r outer' P y l) := by
  rw [rootFreeEndpointMean_congr r outer outer' P y l houter]
  exact rootFreeEndpointBadSet_congr r M G G' P U y z t l c _ hG

end LooseHamilton
