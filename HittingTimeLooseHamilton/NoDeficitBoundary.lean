module

public import HittingTimeLooseHamilton.NoDeficitDeterministic
public import HittingTimeLooseHamilton.PathPerturbationBounds
public import HittingTimeLooseHamilton.PathPerturbationAsymptotic

public section

noncomputable section
namespace LooseHamilton
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Surviving members of the original low-degree set, without recomputing a
threshold after boundary deletion. -/
@[expose] def inheritedBoundaryLowVertices (F : SimpleHypergraph V) (D : Finset V) :
    Finset ↥(univ \ D) := restrictedPorts (univ \ D) (terminalLowVertices F)

@[simp] lemma mem_inheritedBoundaryLowVertices (F : SimpleHypergraph V) (D : Finset V)
    (v : ↥(univ \ D)) :
    v ∈ inheritedBoundaryLowVertices F D ↔ v.val ∈ terminalLowVertices F := by
  exact mem_restrictedPorts _ _ _

lemma inheritedBoundaryLowVertices_card_le (F : SimpleHypergraph V) (D : Finset V) :
    (inheritedBoundaryLowVertices F D).card ≤ (terminalLowVertices F).card :=
  restrictedPorts_card_le _ _

lemma adjustedBoundaryLower_le_original (F : SimpleHypergraph V) (ell : V → ℕ)
    (D : Finset V) (v : ↥(univ \ D)) :
    adjustedBoundaryLower ell D (boundaryEdges D F) v ≤ ell v.val := Nat.sub_le _ _

lemma adjustedBoundaryLower_feasible (F : SimpleHypergraph V) (ell : V → ℕ)
    (D : Finset V) (hell : ∀ v, ell v ≤ vertexDegree F v) :
    ∀ v, adjustedBoundaryLower ell D (boundaryEdges D F) v ≤ vertexDegree (deleteVertices D F) v := by
  intro v
  rw [vertexDegree_deleteVertices]
  have hd := trace_degree_add_core D F v.val
  have he := hell v.val
  change ell v.val - vertexDegree (traceOn D F) v.val ≤ vertexDegree (coreOutside D F) v.val
  omega

/-- Bounded deletion loses at most twice its size at each surviving vertex. -/
lemma bounded_boundary_degree_loss (F : SimpleHypergraph V) (D : Finset V)
    (hp : ∀ u v, u ≠ v → pairDegree F u v ≤ 2) (v : ↥(univ \ D)) :
    vertexDegree F v.val ≤ vertexDegree (deleteVertices D F) v + 2*D.card := by
  have hd := deletion_degree_loss_le F D v.val
  have hs : (∑ y ∈ D, pairDegree F v.val y) ≤ 2*D.card := by
    calc
      _ ≤ ∑ y ∈ D, 2 := sum_le_sum (fun y hy => hp _ _ (by
        intro he; exact (mem_sdiff.mp v.property).2 (he ▸ hy)))
      _ = _ := by simp [Nat.mul_comm]
  rw [vertexDegree_deleteVertices]
  have hm := vertexDegree_mono (filter_subset (fun e=>Disjoint e D) F) v.val
  change vertexDegree (survivingHost F D) v.val ≤ vertexDegree F v.val at hm
  omega

/-- Original slack survives, using the surviving original low set. -/
lemma inherited_boundary_slack (F : SimpleHypergraph V) (ell : V → ℕ)
    (D : Finset V) (a : ℕ)
    (hp : ∀ u v, u ≠ v → pairDegree F u v ≤ 2)
    (hs : ∀ v ∉ terminalLowVertices F, ell v+a+2*D.card ≤ vertexDegree F v) :
    ∀ v ∉ inheritedBoundaryLowVertices F D,
      adjustedBoundaryLower ell D (boundaryEdges D F) v + a ≤ vertexDegree (deleteVertices D F) v := by
  intro v hv
  have hv' : v.val ∉ terminalLowVertices F := by simpa using hv
  have hsl := hs v.val hv'
  have hd := bounded_boundary_degree_loss F D hp v
  have he := adjustedBoundaryLower_le_original F ell D v
  omega

end LooseHamilton
