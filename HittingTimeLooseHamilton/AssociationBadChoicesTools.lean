module

public import HittingTimeLooseHamilton.AssociationModels
public import HittingTimeLooseHamilton.OneVertexSwitchingBasic

public section

noncomputable section
namespace LooseHamilton
open Finset
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]

lemma card_le_uniform_fibres {A C : Type*} [DecidableEq A] [DecidableEq C]
    (s : Finset A) (t : Finset C) (f : A → C) (D : ℕ)
    (hmap : ∀ a ∈ s, f a ∈ t)
    (hf : ∀ b ∈ t, (s.filter (fun a => f a=b)).card ≤ D) : s.card ≤ t.card*D := by
  rw [card_eq_sum_card_fiberwise hmap]
  calc
    _ ≤ ∑ _b ∈ t, D := sum_le_sum hf
    _ = _ := by simp

lemma graphIncidences_vertex_fibre (F : SimpleHypergraph V) (v : V) :
    ((graphIncidences F).filter (fun p => p.2=v)).card = vertexDegree F v := by
  unfold vertexDegree
  apply card_bij (fun p _ => p.1)
  · intro p hp
    obtain ⟨hp,hv⟩ := mem_filter.mp hp
    obtain ⟨he,hm⟩ := (mem_graphIncidences F p).mp hp
    exact mem_filter.mpr ⟨he,hv ▸ hm⟩
  · intro p hp q hq he
    apply Prod.ext he
    exact (mem_filter.mp hp).2.trans (mem_filter.mp hq).2.symm
  · intro e he
    obtain ⟨he,hv⟩ := mem_filter.mp he
    exact ⟨(e,v),by simp [he,hv],rfl⟩

lemma graphIncidences_edge_fibre (F : SimpleHypergraph V) {e : Finset V} (he : e ∈ F) :
    ((graphIncidences F).filter (fun p => p.1=e)).card = e.card := by
  apply card_bij (fun p _ => p.2)
  · intro p hp
    obtain ⟨hp,hv⟩ := mem_filter.mp hp
    exact hv ▸ ((mem_graphIncidences F p).mp hp).2
  · intro p hp q hq hv
    apply Prod.ext _ hv
    exact (mem_filter.mp hp).2.trans (mem_filter.mp hq).2.symm
  · intro v hv
    exact ⟨(e,v),by simp [he,hv],rfl⟩

lemma graphIncidences_heads_card (F : SimpleHypergraph V) (B : Finset V) :
    ((graphIncidences F).filter (fun p => p.2∈B)).card = ∑ v ∈ B, vertexDegree F v := by
  rw [card_eq_sum_card_fiberwise (f := Prod.snd) (t := B) (by intro p hp; exact (mem_filter.mp hp).2)]
  apply sum_congr rfl
  intro v hv
  have he : ((graphIncidences F).filter (fun p => p.2∈B)).filter (fun p => p.2=v) =
      (graphIncidences F).filter (fun p => p.2=v) := by
    ext p
    simp only [mem_filter]
    aesop
  rw [he,graphIncidences_vertex_fibre]

lemma switchedEdge_insert_injective {e : Finset V} {z a b : V}
    (ha : a ∉ e) (hb : b ∉ e) (he : switchedEdge e z a=switchedEdge e z b) : a=b := by
  have hm : a ∈ switchedEdge e z b := by rw [←he]; simp
  rcases (mem_switchedEdge _ _ _ _).mp hm with h | h
  · exact h
  · exact False.elim (ha h.2)

lemma switchedEdge_remove_injective {f : Finset V} {z a b : V}
    (hz : z ∉ f) (ha : a ∈ f) (hb : b ∈ f)
    (he : switchedEdge f a z=switchedEdge f b z) : a=b := by
  by_contra hab
  have hm : a ∈ switchedEdge f b z := (mem_switchedEdge _ _ _ _).mpr (Or.inr ⟨hab,ha⟩)
  rw [←he] at hm
  exact switchedEdge_not_mem ha hz hm
end LooseHamilton
