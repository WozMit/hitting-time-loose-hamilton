module

public import HittingTimeLooseHamilton.DirectedSymmetry
public import HittingTimeLooseHamilton.CompletionMatching

public section

/-! # Complete-host symmetry of the two relative directions

The proof swaps only the endpoints of the newly inserted marker. It acts on
actual edge sets, fixes the prescribed direction of the old root, and is an
involution. Consequently each direction is half the unrestricted completion
count. This statement is specific to the complete host.
-/
noncomputable section
namespace LooseHamilton
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem completionDirectedCount_eq_reverse_complete {r : ℕ}
    {markers : Finset (Finset V)} {P pair : Finset V}
    (hM : IsPairMatching markers) (h : LegalPrivateCompletion r markers P pair)
    (root : ↥markers) (a : ↥root.val) (y z : ↥pair)
    (hpair : pair = {y.val, z.val}) :
    completionDirectedCount r markers (completeEdges V r) P pair h root a y =
      completionDirectedCount r markers (completeEdges V r) P pair h root a z := by
  unfold completionDirectedCount
  rw [inducedHost_completeEdges]
  have hp : (completionRestrictedPair markers P pair).val =
      {completionRestrictedEndpoint h y, completionRestrictedEndpoint h z} := by
    ext x
    simp only [completionRestrictedPair, mem_restrictEdge, hpair,
      mem_insert, mem_singleton]
    simp only [Subtype.ext_iff, completionRestrictedEndpoint]
  exact directedCycleCount_eq_reverse_complete (h.restricted_matching hM) ∅
    (completionRestrictedRoot markers P pair root)
    (completionRestrictedPair markers P pair) (h.restricted_root_ne_pair root)
    (completionRestrictedRootPoint h root a) hp (by simp)

theorem completionCount_eq_twice_directed_complete {r : ℕ}
    {markers : Finset (Finset V)} {P pair : Finset V}
    (hr : 3 ≤ r) (hM : IsPairMatching markers)
    (h : LegalPrivateCompletion r markers P pair)
    (root : ↥markers) (a : ↥root.val) (y z : ↥pair)
    (hpair : pair = {y.val, z.val}) (hyz : y ≠ z) :
    completionCount r markers (completeEdges V r) P pair =
      2 * completionDirectedCount r markers (completeEdges V r) P pair h root a y := by
  rw [completionCount_split hr h root a y z hpair hyz,
    ← completionDirectedCount_eq_reverse_complete hM h root a y z hpair]
  omega

theorem completionDirectedCount_eq_half_complete {r : ℕ}
    {markers : Finset (Finset V)} {P pair : Finset V}
    (hr : 3 ≤ r) (hM : IsPairMatching markers)
    (h : LegalPrivateCompletion r markers P pair)
    (root : ↥markers) (a : ↥root.val) (y z : ↥pair)
    (hpair : pair = {y.val, z.val}) (hyz : y ≠ z) :
    (completionDirectedCount r markers (completeEdges V r) P pair h root a y : ℝ) =
      (completionCount r markers (completeEdges V r) P pair : ℝ) / 2 := by
  have he := completionCount_eq_twice_directed_complete hr hM h root a y z hpair hyz
  rw [he]
  push_cast
  ring

end LooseHamilton
