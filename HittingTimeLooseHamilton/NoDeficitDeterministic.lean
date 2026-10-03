module

public import HittingTimeLooseHamilton.BoundaryDeficit

public section

noncomputable section
namespace LooseHamilton
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Exact partition of a vertex's terminal incidences into kept and sampled edges. -/
lemma batch_vertex_degree_split (F T : SimpleHypergraph V) (v : V) :
    vertexDegree (F \ T) v + vertexDegree (F ∩ T) v = vertexDegree F v := by
  have hd : Disjoint (F \ T) (F ∩ T) := by
    apply disjoint_left.mpr
    intro e he hf
    exact (mem_sdiff.mp he).2 (mem_inter.mp hf).2
  have hu : (F \ T) ∪ (F ∩ T) = F := by ext e; simp; tauto
  rw [← vertexDegree_union hd,hu]

/-- Any failed lower bound after a batch either loses an incidence at an
original low vertex or loses at least the stipulated slack elsewhere. -/
theorem no_deficit_failure_split (F : SimpleHypergraph V) (ell : V → ℕ)
    (B : Finset V) (T : SimpleHypergraph V) (a : ℕ)
    (hell : ∀ v, ell v ≤ vertexDegree F v)
    (hslack : ∀ v ∉ B, ell v+a ≤ vertexDegree F v)
    (hfail : ∃ v, vertexDegree (F \ T) v < ell v) :
    (∃ v ∈ B, 1 ≤ vertexDegree (F ∩ T) v) ∨
      (∃ v, a ≤ vertexDegree (F ∩ T) v) := by
  obtain ⟨v,hv⟩ := hfail
  have hd := batch_vertex_degree_split F T v
  by_cases hb : v ∈ B
  · left; refine ⟨v,hb,?_⟩
    have he := hell v
    omega
  · right; refine ⟨v,?_⟩
    have hs := hslack v hb
    omega

/-- Equivalent containment with the paper's edge-hitting event. -/
theorem no_deficit_failure_edge_split (F : SimpleHypergraph V) (ell : V → ℕ)
    (B : Finset V) (T : SimpleHypergraph V) (a : ℕ)
    (hell : ∀ v, ell v ≤ vertexDegree F v)
    (hslack : ∀ v ∉ B, ell v+a ≤ vertexDegree F v)
    (hfail : ∃ v, vertexDegree (F \ T) v < ell v) :
    (∃ e ∈ F ∩ T, ¬Disjoint e B) ∨ (∃ v, a ≤ vertexDegree (F ∩ T) v) := by
  rcases no_deficit_failure_split F ell B T a hell hslack hfail with hlow | hlarge
  · left
    obtain ⟨v,hv,hd⟩ := hlow
    obtain ⟨e,he⟩ := card_pos.mp (show 0 < ((F ∩ T).filter (fun e=>v∈e)).card from hd)
    exact ⟨e,(mem_filter.mp he).1,fun hh=>disjoint_left.mp hh (mem_filter.mp he).2 hv⟩
  · exact Or.inr hlarge

end LooseHamilton
