module

public import HittingTimeLooseHamilton.BoundaryDeficitBasic
public import HittingTimeLooseHamilton.BoundaryModels

public section

noncomputable section
namespace LooseHamilton
open Finset
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]

lemma terminalDeletionDeficit_eq_ambient_sum (F : SimpleHypergraph V)
    (ell : V → ℕ) (Z : Finset V) :
    terminalDeletionDeficit F ell Z =
      ∑ v ∈ (univ \ Z), (ell v - vertexDegree (survivingHost F Z) v) := by
  unfold terminalDeletionDeficit
  simp_rw [vertexDegree_deleteVertices]
  exact sum_coe_sort _ (fun v => ell v - vertexDegree (survivingHost F Z) v)

/-- Exact deterministic comparison of the post-boundary single-root deficit
with the original single-root deficit. No regularity or probability assumption
is needed, and the induced graph is on the actual surviving subtype. -/
theorem boundary_single_root_deficit_le (F : SimpleHypergraph V) (ell : V → ℕ)
    (D : Finset V) (y : ↥(univ \ D)) :
    terminalDeletionDeficit (deleteVertices D F)
        (adjustedBoundaryLower ell D (boundaryEdges D F)) {y} ≤
      terminalDeletionDeficit F ell {y.val} := by
  classical
  rw [terminalDeletionDeficit_eq_ambient_sum,terminalDeletionDeficit_eq_ambient_sum]
  let S : Finset ↥(univ \ D) := univ \ {y}
  let f : V → ℕ := fun v => ell v - vertexDegree (survivingHost F {y.val}) v
  have hpoint : ∀ v ∈ S,
      (adjustedBoundaryLower ell D (boundaryEdges D F) v -
        vertexDegree (survivingHost (deleteVertices D F) {y}) v) ≤ f v.val := by
    intro v hv
    exact boundary_single_root_deficit_pointwise F ell D y v
  have hsub : S.image Subtype.val ⊆ univ \ {y.val} := by
    intro v hv
    obtain ⟨w,hw,rfl⟩ := mem_image.mp hv
    apply mem_sdiff.mpr
    refine ⟨mem_univ _, ?_⟩
    intro hh
    have hwy : w = y := Subtype.ext (mem_singleton.mp hh)
    subst w
    exact (mem_sdiff.mp hw).2 (mem_singleton_self _)
  calc
    _ ≤ ∑ v ∈ S, f v.val := sum_le_sum hpoint
    _ = ∑ v ∈ S.image Subtype.val, f v := by
      rw [sum_image]
      exact fun v hv w hw he => Subtype.ext he
    _ ≤ ∑ v ∈ (univ \ {y.val}), f v := sum_le_sum_of_subset_of_nonneg hsub (by intros; omega)

/-- The comparison also applies when the observed boundary is named separately. -/
theorem boundary_single_root_deficit_le_of_eq (F : SimpleHypergraph V)
    (ell : V → ℕ) (D : Finset V) (A : SimpleHypergraph V)
    (hA : boundaryEdges D F = A) (y : ↥(univ \ D)) :
    terminalDeletionDeficit (deleteVertices D F) (adjustedBoundaryLower ell D A) {y} ≤
      terminalDeletionDeficit F ell {y.val} := by
  subst A
  exact boundary_single_root_deficit_le F ell D y

end LooseHamilton
