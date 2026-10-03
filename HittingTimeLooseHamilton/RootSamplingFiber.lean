module

public import HittingTimeLooseHamilton.RootSamplingStrata
public import HittingTimeLooseHamilton.RootLinkConditionalReduction

public section

/-! Exact reduction of a positive prescribed-inner stratum to the feasible nested-link tail. -/
noncomputable section
namespace LooseHamilton
open Finset
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- This finite reduction exposes all hypotheses needed by the independent nested-link tail lemma. -/
lemma root_sampling_fiber_transfer (r M : ℕ) (ell : V → ℕ)
    [Nonempty (TerminalState V r M ell)] (m : ℕ) (hMm : M ≤ m)
    (hm : m ≤ (completeEdges V r).card) (y : V) (F₀ H₀ R I Γ : SimpleHypergraph V)
    (hΓ : Γ ⊆ rootEdgeUniverse r y) (hR : R ⊆ rootEdgeUniverse r y)
    (hH₀ : Disjoint H₀ (rootEdgeUniverse r y))
    (hδ : ∑v,rootAdjustedDeficit y ell F₀ v ≤ 1)
    (hobs : 0 < (extensionLaw r M ell).event (fun ω =>
      RootLinkObservation (rootEdgeUniverse r y\R) (F₀∪I) (H₀∪R)
        ω.1.val (extensionState ω.1 ω.2 m)))
    (γ : ℝ)
    (htail : ∀ hne : Nonempty (RootLinkFeasibleState (rootEdgeUniverse r y\R) (F₀∪I) ell
        (M-(F₀∪I).card) (m-(H₀∪R).card)),
      letI := hne
      (∀p : FiniteNestedSubsets (rootEdgeUniverse r y\R) (M-(F₀∪I).card) (m-(H₀∪R).card),
        ∀v,ell v ≤ vertexDegree ((F₀∪I)∪p.val.1) v) ∨
      (∃ S : SimpleHypergraph V,S ⊆ rootEdgeUniverse r y\R ∧
        ∀p : FiniteNestedSubsets (rootEdgeUniverse r y\R) (M-(F₀∪I).card) (m-(H₀∪R).card),
          (∀v,ell v ≤ vertexDegree ((F₀∪I)∪p.val.1) v) ↔ ¬Disjoint p.val.1 S) →
      (FiniteEntropy.uniform : FiniteEntropy.Law
        (RootLinkFeasibleState (rootEdgeUniverse r y\R) (F₀∪I) ell
          (M-(F₀∪I).card) (m-(H₀∪R).card))).event
        (fun p=>2*(m-H₀.card) ≤ 3*((p.val.val.2∪R)∩Γ).card) ≤ γ) :
    ((extensionLaw r M ell).condition (fun ω =>
      RootLinkObservation (rootEdgeUniverse r y\R) (F₀∪I) (H₀∪R)
        ω.1.val (extensionState ω.1 ω.2 m)) hobs).event
      (fun ω=>RootLinkBad Γ (m-H₀.card) (rootSamplingPair r M ell m ω)) ≤ γ := by
  let U := rootEdgeUniverse r y\R
  have hU : U ⊆ completeEdges V r := sdiff_subset.trans (filter_subset _ _)
  have hUy : ∀e∈U,y∈e := by
    intro e he
    exact (mem_filter.mp (mem_sdiff.mp he).1).2
  have hδ' : ∑v,rootAdjustedDeficit y ell (F₀∪I) v ≤ 1 :=
    (rootAdjustedDeficit_sum_mono y ell subset_union_left).trans hδ
  obtain ⟨hne,hlaw⟩ := root_link_conditional_law r M ell m hMm hm U (F₀∪I) (H₀∪R) hU hobs
  letI := hne
  have hc := observed_root_link_constraint_zero_or_star r M ell m hMm hm U (F₀∪I) (H₀∪R)
    y hUy hobs hδ'
  have hc' : (∀p : FiniteNestedSubsets U (M-(F₀∪I).card) (m-(H₀∪R).card),
      ∀v,ell v ≤ vertexDegree ((F₀∪I)∪p.val.1) v) ∨
      (∃S : SimpleHypergraph V,S ⊆ U ∧
        ∀p : FiniteNestedSubsets U (M-(F₀∪I).card) (m-(H₀∪R).card),
          (∀v,ell v ≤ vertexDegree ((F₀∪I)∪p.val.1) v) ↔ ¬Disjoint p.val.1 S) := by
    rcases hc with hc | ⟨v,hvy,hc⟩
    · exact Or.inl hc
    · exact Or.inr ⟨rootLinkStar U v,filter_subset _ _,hc⟩
  have hcongr := conditional_event_congr_on (extensionLaw r M ell)
    (fun ω=>RootLinkObservation U (F₀∪I) (H₀∪R) ω.1.val (extensionState ω.1 ω.2 m))
    (fun ω=>RootLinkBad Γ (m-H₀.card) (rootSamplingPair r M ell m ω))
    (fun ω=>2*(m-H₀.card) ≤ 3*(((extensionState ω.1 ω.2 m∩U)∪R)∩Γ).card) hobs (by
      intro ω hω
      have he := root_complement_bad_count (extensionState ω.1 ω.2 m) U H₀ R Γ hω.2
        (hH₀.mono_right hΓ)
      change 2*(m-H₀.card) ≤ 3*(extensionState ω.1 ω.2 m∩Γ).card ↔ _
      rw [he])
  rw [hcongr,hlaw (fun p=>2*(m-H₀.card) ≤ 3*((p.2∪R)∩Γ).card)]
  exact htail hne hc'
end LooseHamilton
