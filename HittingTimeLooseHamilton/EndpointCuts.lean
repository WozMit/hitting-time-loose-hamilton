module

public import HittingTimeLooseHamilton.EndpointCutExhaustive
public import HittingTimeLooseHamilton.EndpointExpansionFamilies
public import HittingTimeLooseHamilton.EndpointCutCardinality

public section

/-! # Section 9: endpoint cuts and equation (cutpartition)

The public partition counts independent core cycles in the fixed induced host.
No cut-partition or surgery hypothesis is assumed: the local constructions,
exhaustive classification and joint recovery are proved in the imported modules.
The explicit size threshold rules out short cores in the manuscript's large-N
setting. Original-port prohibition is always imposed using the fixed set `U`.
-/
noncomputable section
namespace LooseHamilton
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {r : ℕ} {M G : Finset (Finset V)} {P U : Finset V} {y z : V}

/-- Both geometric expansions provide actual source cycles and their intrinsic
edge roles. This closes the local obligations of the finite-family bijection. -/
theorem endpointCut_expansion_properties (hr : 3 ≤ r)
    (hs : LegalPrivateCompletion r M P {y,z})
    (hM : (M : Set (Finset V)).PairwiseDisjoint id) :
    EndpointCutExpansionProperties r M G P y z := by
  constructor
  · intro l hl F hF
    exact endpointCut_expand_I hr hs hM hl hF
  · intro l hl F hF
    exact endpointCut_expand_II hr hs hM hl hF

/-- Exact disjoint partition of actual source edge sets into both core types. -/
theorem endpoint_cut_partition_families (hr : 3 ≤ r)
    (hs : LegalPrivateCompletion r M P {y,z})
    (hM : (M : Set (Finset V)).PairwiseDisjoint id)
    (hports : EndpointSourcePorts U M y z) (hG : G ⊆ allowedEdges r U)
    (hsize : 5 * (r - 1) < (univ \ P).card) :
    completionCount r M G P {y,z} =
      (∑ l ∈ endpointCutLabelsI r M G P y z,
        (endpointCutCoreFamilyI r M G P y z l).card) +
      ∑ l ∈ endpointCutLabelsII r M G P y z,
        (endpointCutCoreFamilyII r M G P y z l).card := by
  exact endpointCut_partition_of_surgeries (endpointCut_expansion_properties hr hs hM)
    (endpointCut_contraction_exhaustive hr hs hports hG hsize) hM
    (fun hy => hports.root_ordinary (hports.old_ports hy))

/-- Equation (cutpartition): `W_G(P;yz) = ∑_b X_b`.
The two sums are the disjoint Type I and Type II label sets, and each summand
is exactly `X` on its surviving vertex subtype and fixed induced host. -/
theorem endpoint_cut_partition (hr : 3 ≤ r)
    (hs : LegalPrivateCompletion r M P {y,z})
    (hM : (M : Set (Finset V)).PairwiseDisjoint id)
    (hports : EndpointSourcePorts U M y z) (hG : G ⊆ allowedEdges r U)
    (hsize : 5 * (r - 1) < (univ \ P).card) :
    completionCount r M G P {y,z} =
      (∑ l ∈ endpointCutLabelsI r M G P y z,
        unrestrictedCycleCount r
          (restrictEdges (univ \ (P ∪ l.deleted y)) (l.markers M z))
          (inducedHost (univ \ (P ∪ l.deleted y)) G)) +
      ∑ l ∈ endpointCutLabelsII r M G P y z,
        unrestrictedCycleCount r
          (restrictEdges (univ \ (P ∪ l.deleted y)) (l.markers M z))
          (inducedHost (univ \ (P ∪ l.deleted y)) G) := by
  rw [endpoint_cut_partition_families hr hs hM hports hG hsize]
  congr 1
  · apply sum_congr rfl
    intro l hl
    exact endpointCutCoreCountI_eq_X hr hs ((mem_endpointCutLabelsI _ _ _ _ _ _ _).mp hl)
  · apply sum_congr rfl
    intro l hl
    exact endpointCutCoreCountII_eq_X hr hs hM ((mem_endpointCutLabelsII _ _ _ _ _ _ _).mp hl)

end LooseHamilton
