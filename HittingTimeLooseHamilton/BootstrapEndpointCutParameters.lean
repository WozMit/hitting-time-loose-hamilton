module

public import HittingTimeLooseHamilton.BootstrapEndpointComparison
public import HittingTimeLooseHamilton.EndpointRootEventMobility
public import HittingTimeLooseHamilton.BootstrapSourceMeanRatios

public section

noncomputable section
namespace LooseHamilton.BootstrapEndpointCutParameters
open Finset BootstrapBases
variable {V : Type} [Fintype V] [DecidableEq V]
variable {r : ℕ} {M G : SimpleHypergraph V} {P : Finset V} {y z : V}

theorem raw_legal (k : EndpointMigrationCut r M G P y z) :
    BootstrapEndpointComparison.CutLegal r M G P y z (endpointMigrationRawLabel k) := by
  cases k with
  | inl k => exact (mem_endpointCutLabelsI _ _ _ _ _ _ _).mp k.property
  | inr k => exact (mem_endpointCutLabelsII _ _ _ _ _ _ _).mp k.property

theorem raw_sizes (k : EndpointMigrationCut r M G P y z) :
    match endpointMigrationRawLabel k with
    | .inl l => l.2.card = r-2
    | .inr l => l.2.2.2.1.card = r-2 ∧ l.2.2.2.2.card = r-2 := by
  cases k with
  | inl k => exact ((mem_endpointCutLabelsI _ _ _ _ _ _ _).mp k.property).private_card
  | inr k =>
    have h := (mem_endpointCutLabelsII _ _ _ _ _ _ _).mp k.property
    exact ⟨h.first_private_card,h.second_private_card⟩

theorem base_card_bounds {original : SimpleHypergraph V} (b : Base original) :
    Fintype.card V-1 ≤ Fintype.card ↥(active b) ∧ Fintype.card ↥(active b) ≤ Fintype.card V := by
  have hD := deleted_card_le b
  have hc : Fintype.card ↥(active b) = (active b).card := Fintype.card_coe _
  rw [hc]
  simp only [active,card_sdiff_of_subset (subset_univ _),card_univ]
  omega

theorem source_room {original : SimpleHypergraph V} (b : Base original)
    (hr : 3 ≤ r) (hN : 8*r ≤ Fintype.card V) (P : Finset ↥(active b))
    (hP : P.card = r-2) : 5*(r-1) < (univ \ P).card := by
  have hn := (base_card_bounds b).1
  rw [card_sdiff_of_subset (subset_univ _),card_univ,hP]
  omega

theorem residual_matching {original : SimpleHypergraph V} (hM : IsPairMatching original)
    (b : Base original) : IsPairMatching (restrictEdges (active b) (markers hM b)) :=
  (markers_matching hM b).restrict (active b) (fun e he => markers_retained hM b he)

theorem filtered_subset_allowed (r : ℕ) (A : Finset V) (H : SimpleHypergraph V)
    (hH : H ⊆ completeEdges V r) (U : Finset ↥A) :
    fixedPortHost (inducedHost A H) U ⊆ allowedEdges r U := by
  intro e he
  obtain ⟨heH,heU⟩ := mem_filter.mp he
  apply (mem_allowedEdges _ _ _).mpr
  refine ⟨?_,heU⟩
  have hc := (mem_completeEdges _ _).mp (hH ((mem_inducedHost _ _ _).mp heH))
  simpa only [ambientEdge,card_map] using hc

end LooseHamilton.BootstrapEndpointCutParameters
