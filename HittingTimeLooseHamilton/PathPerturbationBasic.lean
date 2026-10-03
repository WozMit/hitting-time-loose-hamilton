module

public import HittingTimeLooseHamilton.TerminalDeletionInduced
public import HittingTimeLooseHamilton.CoreFiniteBounds

public section

noncomputable section
namespace LooseHamilton
open Finset
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Deleting vertices removes at most their total number of incidences. -/
theorem deletion_edge_loss_le (F : SimpleHypergraph V) (Z : Finset V) :
    F.card - (survivingHost F Z).card ≤ ∑ v ∈ Z, vertexDegree F v := by
  have hc := coreOutside_card Z F
  have ht := trace_card_le_degree_sum Z F
  change F.card - (coreOutside Z F).card ≤ _
  omega

lemma deleteVertices_card (F : SimpleHypergraph V) (Z : Finset V) :
    (deleteVertices Z F).card = (survivingHost F Z).card := by
  rw [deleteVertices, ← restricted_core_eq_inducedHost]
  apply restrictEdges_card_of_supported
  intro e he x hx
  exact mem_sdiff.mpr ⟨mem_univ _, fun hz =>
    disjoint_left.mp ((mem_coreOutside _ _ _).mp he).2 hx hz⟩

/-- Any edge property loses at most the number of removed edges. -/
theorem filter_card_loss_le {F G : SimpleHypergraph V} (hGF : G ⊆ F)
    (P : Finset V → Prop) [DecidablePred P] :
    (F.filter P).card - (G.filter P).card ≤ F.card - G.card := by
  have heq : F.filter P \ G.filter P = (F \ G).filter P := by
    ext e; simp only [mem_sdiff, mem_filter]; tauto
  have h := card_le_card (filter_subset P (F \ G))
  rw [← heq, card_sdiff_of_subset (filter_subset_filter P hGF),
    card_sdiff_of_subset hGF] at h
  exact h

/-- Generic discrepancy transfer after a bounded number of edge removals,
with the centre adjusted to the new edge count. -/
theorem filter_discrepancy_transfer {F G : SimpleHypergraph V} (hGF : G ⊆ F)
    (P : Finset V → Prop) [DecidablePred P] (theta E : ℝ)
    (htheta : 0 ≤ theta)
    (hE : |((F.filter P).card : ℝ) - theta * F.card| ≤ E) :
    |((G.filter P).card : ℝ) - theta * G.card| ≤
      E + (1 + theta) * ((F.card - G.card : ℕ) : ℝ) := by
  have hcards : G.card ≤ F.card := card_le_card hGF
  have hcounts : (G.filter P).card ≤ (F.filter P).card :=
    card_le_card (filter_subset_filter P hGF)
  have hloss := filter_card_loss_le hGF P
  have hlossR : ((F.filter P).card : ℝ) - (G.filter P).card ≤
      (F.card : ℝ) - G.card := by
    exact_mod_cast (show ((F.filter P).card - (G.filter P).card : ℕ) ≤ F.card-G.card from hloss)
  rw [Nat.cast_sub hcards]
  have hcR : (G.card : ℝ) ≤ F.card := by exact_mod_cast hcards
  have hdR : ((G.filter P).card : ℝ) ≤ (F.filter P).card := by exact_mod_cast hcounts
  rw [abs_le] at hE ⊢
  constructor <;> nlinarith

/-- Filtering out every edge meeting a fixed port set twice. -/
@[expose] def portFilteredHost (U : Finset V) (F : SimpleHypergraph V) : SimpleHypergraph V :=
  F.filter (fun e => (e ∩ U).card ≤ 1)

lemma portFilteredHost_subset (U : Finset V) (F : SimpleHypergraph V) :
    portFilteredHost U F ⊆ F := filter_subset _ _

theorem port_filter_edge_loss_le (U : Finset V) (F : SimpleHypergraph V) :
    F.card - (portFilteredHost U F).card ≤ ∑ v ∈ U, vertexDegree F v := by
  have hsub : survivingHost F U ⊆ portFilteredHost U F := by
    intro e he
    obtain ⟨he,hd⟩ := mem_filter.mp he
    apply mem_filter.mpr
    refine ⟨he, ?_⟩
    have hi : e ∩ U = ∅ := disjoint_iff_inter_eq_empty.mp hd
    simp [hi]
  have hc := card_le_card hsub
  exact (Nat.sub_le_sub_left hc F.card).trans (deletion_edge_loss_le F U)

theorem port_filter_vertex_degree_le (U : Finset V) (F : SimpleHypergraph V) (v : V) :
    vertexDegree (portFilteredHost U F) v ≤ vertexDegree F v :=
  vertexDegree_mono (portFilteredHost_subset U F) v

theorem port_filter_pair_degree_le (U : Finset V) (F : SimpleHypergraph V) (v w : V) :
    pairDegree (portFilteredHost U F) v w ≤ pairDegree F v w :=
  pairDegree_mono (portFilteredHost_subset U F) v w

end LooseHamilton
