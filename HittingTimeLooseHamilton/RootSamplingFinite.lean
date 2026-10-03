module

public import HittingTimeLooseHamilton.RootSamplingFiber
public import HittingTimeLooseHamilton.RootConditionalMixture
public import HittingTimeLooseHamilton.RootSamplingSpecializedTail

public section

/-! Finite root-link sampling under Q, with prescribed-inner statuses averaged out. -/
noncomputable section
set_option maxHeartbeats 300000
namespace LooseHamilton
open Finset
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The finite form of Lemma 5.6 for genuine root-free observations.
The prescribed current edges are observed present, but their terminal status is not observed. -/
theorem root_link_sampling_finite (r M : ℕ) (ell : V → ℕ)
    [Nonempty (TerminalState V r M ell)] (m : ℕ) (hMm : M ≤ m)
    (hm : m ≤ (completeEdges V r).card) (y : V) (F₀ H₀ R Γ : SimpleHypergraph V) (h : ℕ)
    (hΓ : Γ ⊆ rootEdgeUniverse r y) (hR : R ⊆ rootEdgeUniverse r y) (hRh : R.card ≤ h)
    (hU : 0 < (rootEdgeUniverse r y).card) (hh : 2*h ≤ (rootEdgeUniverse r y).card)
    (hq : 12*(h+1) ≤ m-H₀.card)
    (hδ : ∑v,rootAdjustedDeficit y ell F₀ v ≤ 1)
    (hρ : rootLinkDensity r y Γ ≤ 1/8)
    (hE : 0 < (extensionLaw r M ell).event
      (fun ω=>RootFreeObservation y F₀ H₀ R (rootSamplingPair r M ell m ω))) :
    ((extensionLaw r M ell).condition
      (fun ω=>RootFreeObservation y F₀ H₀ R (rootSamplingPair r M ell m ω)) hE).event
      (fun ω=>RootLinkBad Γ (m-H₀.card) (rootSamplingPair r M ell m ω)) ≤
        (8*rootLinkDensity r y Γ)^(((m-H₀.card:ℕ):ℝ)/4) := by
  classical
  have hρ0 : 0 ≤ rootLinkDensity r y Γ := by unfold rootLinkDensity; positivity
  have hρsmall : 8*rootLinkDensity r y Γ ≤ 1 := by linarith
  obtain ⟨ω₀,hω₀⟩ := exists_of_event_pos (extensionLaw r M ell) _ hE
  have hF₀ : Disjoint F₀ (rootEdgeUniverse r y) := by
    have he : rootFreeEdges y ω₀.1.val=F₀ := hω₀.1
    simpa only [he] using rootFreeEdges_disjoint_root r y ω₀.1.val
  have hH₀ : Disjoint H₀ (rootEdgeUniverse r y) := by
    have he : rootFreeEdges y (extensionState ω₀.1 ω₀.2 m)=H₀ := hω₀.2.1
    simpa only [he] using rootFreeEdges_disjoint_root r y (extensionState ω₀.1 ω₀.2 m)
  apply conditional_event_le_of_fibre_bounds (extensionLaw r M ell)
    (fun ω=>RootFreeObservation y F₀ H₀ R (rootSamplingPair r M ell m ω))
    (fun ω=>RootLinkBad Γ (m-H₀.card) (rootSamplingPair r M ell m ω))
    (fun ω=>ω.1.val∩R) hE _
  intro I hi
  obtain ⟨ωI,hωI⟩ := exists_of_event_pos (extensionLaw r M ell) _ hi
  have hIR : I ⊆ R := by
    have he : ωI.1.val∩R=I := hωI.2
    simpa only [he] using (inter_subset_right : ωI.1.val∩R ⊆ R)
  have hstratum : (fun ω : TerminalState V r M ell × MissingOrder V r M =>
      RootFreeObservation y F₀ H₀ R (rootSamplingPair r M ell m ω) ∧ ω.1.val∩R=I) =
      (fun ω=>RootLinkObservation (rootEdgeUniverse r y\R) (F₀∪I) (H₀∪R)
        ω.1.val (extensionState ω.1 ω.2 m)) := by
    funext ω
    apply propext
    simpa only [RootFreeObservation,rootSamplingPair,and_assoc] using
      (root_link_prescribed_observation_iff r y ω.1.val (extensionState ω.1 ω.2 m) F₀ H₀ R I
        ω.1.property.1 (extensionState_subset ω.1 ω.2 m) hR hF₀ hH₀ hIR).symm
  have hobs : 0 < (extensionLaw r M ell).event
      (fun ω=>RootLinkObservation (rootEdgeUniverse r y\R) (F₀∪I) (H₀∪R)
        ω.1.val (extensionState ω.1 ω.2 m)) := by simpa only [hstratum] using hi
  have hbound := root_sampling_fiber_transfer r M ell m hMm hm y F₀ H₀ R I Γ hΓ hR hH₀ hδ hobs
    ((8*rootLinkDensity r y Γ)^(((m-H₀.card:ℕ):ℝ)/4)) (by
      intro hne hc
      letI := hne
      obtain ⟨p⟩ := hne
      have hqU : m-(H₀∪R).card ≤ (rootEdgeUniverse r y\R).card := by
        have hp := mem_powersetCard.mp p.val.property.2.2
        rw [←hp.2]
        exact card_le_card hp.1
      have hqQ : m-(H₀∪R).card ≤ m-H₀.card :=
        Nat.sub_le_sub_left (card_le_card (subset_union_left : H₀ ⊆ H₀∪R)) m
      obtain ⟨hU',hden⟩ := root_remaining_density r y Γ R h hR hRh hU hh
      exact root_link_feasible_tail (rootEdgeUniverse r y\R) (F₀∪I) Γ R ell
        (M-(F₀∪I).card) (m-(H₀∪R).card) (m-H₀.card) h (rootLinkDensity r y Γ)
        hqU hU' hqQ hq hRh hρ0 hρsmall hden hc)
  simpa only [hstratum] using hbound
end LooseHamilton
