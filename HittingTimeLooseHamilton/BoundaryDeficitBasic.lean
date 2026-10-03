module

public import HittingTimeLooseHamilton.PathPerturbationInduced
public import HittingTimeLooseHamilton.TerminalRegularityModels

public section

noncomputable section
namespace LooseHamilton
open Finset
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Removing one vertex loses exactly the edges counted by its codegree. -/
lemma vertexDegree_singleton_deletion (F : SimpleHypergraph V) (y v : V) :
    vertexDegree (survivingHost F {y}) v = vertexDegree F v - pairDegree F v y := by
  classical
  have hpart := card_filter_add_card_filter_not (s:=F.filter (fun e=>v∈e)) (p:=fun e=>y∈e)
  have hp : ((F.filter (fun e=>v∈e)).filter (fun e=>y∈e)).card = pairDegree F v y := by
    simp only [filter_filter,pairDegree]
  have hd : ((F.filter (fun e=>v∈e)).filter (fun e=>y∉e)).card =
      vertexDegree (survivingHost F {y}) v := by
    simp only [filter_filter,vertexDegree,survivingHost,disjoint_singleton_right]
    congr 2; ext e; simp [and_comm]
  rw [hp,hd] at hpart
  change pairDegree F v y + vertexDegree (survivingHost F {y}) v = vertexDegree F v at hpart
  omega

/-- Exposing a boundary and subtracting its exact degree contribution cannot
increase any subsequent one-root deficit. -/
lemma boundary_single_root_deficit_pointwise (F : SimpleHypergraph V) (ell : V → ℕ)
    (D : Finset V) (y v : ↥(univ \ D)) :
    (ell v.val - vertexDegree (traceOn D F) v.val) -
        vertexDegree (survivingHost (deleteVertices D F) {y}) v ≤
      ell v.val - vertexDegree (survivingHost F {y.val}) v.val := by
  rw [vertexDegree_singleton_deletion,vertexDegree_singleton_deletion,
    vertexDegree_deleteVertices,pairDegree_deleteVertices]
  have hpart := trace_degree_add_core D F v.val
  change vertexDegree (traceOn D F) v.val + vertexDegree (survivingHost F D) v.val =
    vertexDegree F v.val at hpart
  have hp := pairDegree_mono (filter_subset (fun e=>Disjoint e D) F) v.val y.val
  change pairDegree (survivingHost F D) v.val y.val ≤ pairDegree F v.val y.val at hp
  have hpd : pairDegree (survivingHost F D) v.val y.val ≤ vertexDegree (survivingHost F D) v.val := by
    apply card_le_card
    intro e he
    exact mem_filter.mpr ⟨(mem_filter.mp he).1,(mem_filter.mp he).2.1⟩
  omega

end LooseHamilton
