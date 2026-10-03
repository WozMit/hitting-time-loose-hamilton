module

public import HittingTimeLooseHamilton.EndpointCutLegalBounds
public import HittingTimeLooseHamilton.Operations

public section

/-! # The manuscript's degree and polynomial bounds for all labelled cuts -/
namespace LooseHamilton
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Both types are counted once, with every private block and junction labelled. -/
@[expose] noncomputable def endpointCutLabelCount (r : ℕ) (M G : Finset (Finset V))
    (P : Finset V) (y z : V) : ℕ :=
  (endpointCutLabelsI r M G P y z).card + (endpointCutLabelsII r M G P y z).card

theorem endpoint_cut_count_bound {r : ℕ} {M G H : Finset (Finset V)}
    {P : Finset V} {y z : V} (hG : G ⊆ H) (hH : H ⊆ completeEdges V r)
    (hM : (M : Set (Finset V)).PairwiseDisjoint id) (hy : y ∉ originalPorts M) :
    endpointCutLabelCount r M G P y z ≤
      (r - 1) * vertexDegree H y +
        (r - 1)^2 * vertexDegree H y * maxVertexDegree H := by
  apply legalEndpointCutLabels_card_le hG hH hM hy
  intro v
  exact le_sup (f := vertexDegree H) (mem_univ v)

/-- An explicit `r`-dependent constant witnesses the stated `O_r(N^(2r-2))`. -/
theorem endpoint_cut_count_polynomial {r : ℕ} {M G H : Finset (Finset V)}
    {P : Finset V} {y z : V} (hr : 3 ≤ r) (hG : G ⊆ H)
    (hH : H ⊆ completeEdges V r)
    (hM : (M : Set (Finset V)).PairwiseDisjoint id) (hy : y ∉ originalPorts M) :
    endpointCutLabelCount r M G P y z ≤
      ((r - 1) + (r - 1)^2) * (Fintype.card V) ^ (2*r-2) :=
  legalEndpointCutLabels_card_le_polynomial (by omega) hG hH hM hy

end LooseHamilton
