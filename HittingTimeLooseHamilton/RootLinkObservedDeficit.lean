module

public import HittingTimeLooseHamilton.RootLinkConditionalLaw
public import HittingTimeLooseHamilton.RootLinkDeficit

public section

/-! Feasible observed data discharge the root's own lower bound automatically. -/
noncomputable section
namespace LooseHamilton
open Finset
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]

lemma root_link_observed_root_bound (r M : ℕ) (ell : V → ℕ) (m : ℕ)
    (U A B : SimpleHypergraph V) (y : V) (hUy : ∀e∈U,y∈e)
    (W : RootLinkFiber r M ell m U A B) :
    Disjoint A U ∧ ell y ≤ vertexDegree A y+(M-A.card) := by
  have hAU : Disjoint A U := by rw [←W.property.1]; exact sdiff_disjoint
  refine ⟨hAU,?_⟩
  let p := rootLinkRestrict r M ell m U A B W
  have hi := p.val.property.1.trans (mem_powersetCard.mp p.val.property.2.2).1
  have hf := p.property y
  rw [vertexDegree_union (hAU.mono_right hi),root_inner_degree U y hUy hi,
    p.val.property.2.1] at hf
  exact hf

/-- Positive actual root-free observations imply the root-size condition, so the
only residual feasibility restriction is none or one non-root star hit. -/
theorem observed_root_link_constraint_zero_or_star (r M : ℕ) (ell : V → ℕ)
    [Nonempty (TerminalState V r M ell)] (m : ℕ) (hMm : M ≤ m)
    (hm : m ≤ (completeEdges V r).card) (U A B : SimpleHypergraph V)
    (y : V) (hUy : ∀e∈U,y∈e)
    (hobs : 0 < (extensionLaw r M ell).event (fun ω =>
      RootLinkObservation U A B ω.1.val (extensionState ω.1 ω.2 m)))
    (hδ : ∑ v,rootAdjustedDeficit y ell A v ≤ 1) :
    (∀ p : FiniteNestedSubsets U (M-A.card) (m-B.card), ∀v,
      ell v ≤ vertexDegree (A∪p.val.1) v) ∨
      ∃ v : V,v≠y ∧ ∀ p : FiniteNestedSubsets U (M-A.card) (m-B.card),
        (∀w,ell w ≤ vertexDegree (A∪p.val.1) w) ↔ ¬Disjoint p.val.1 (rootLinkStar U v) := by
  obtain ⟨ω,hω⟩ := exists_of_event_pos (extensionLaw r M ell) _ hobs
  let W : RootLinkFiber r M ell m U A B :=
    ⟨extensionNestedState r M ell m hMm hm ω,hω⟩
  obtain ⟨hAU,hroot⟩ := root_link_observed_root_bound r M ell m U A B y hUy W
  exact root_link_constraint_zero_or_star U A ell y hUy hAU _ _ hroot hδ
end LooseHamilton
