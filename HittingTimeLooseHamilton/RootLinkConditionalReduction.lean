module

public import HittingTimeLooseHamilton.RootLinkObservedDeficit

public section

/-! Converting the exact feasible-pair law to the unrestricted or single-star conditioned law. -/
noncomputable section
namespace LooseHamilton
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
attribute [local instance] Classical.propDecidable

lemma root_link_feasible_nonempty_nested (U A : SimpleHypergraph V) (ell : V → ℕ) (b q : ℕ)
    [Nonempty (RootLinkFeasibleState U A ell b q)] : Nonempty (FiniteNestedSubsets U b q) := by
  obtain ⟨p⟩ := ‹Nonempty (RootLinkFeasibleState U A ell b q)›
  exact ⟨p.val⟩

lemma root_link_unrestricted_uniform (U A : SimpleHypergraph V) (ell : V → ℕ) (b q : ℕ)
    [Nonempty (RootLinkFeasibleState U A ell b q)] [Nonempty (FiniteNestedSubsets U b q)]
    (hall : ∀ p : FiniteNestedSubsets U b q, ∀v,ell v ≤ vertexDegree (A∪p.val.1) v)
    (P : SimpleHypergraph V × SimpleHypergraph V → Prop) :
    (FiniteEntropy.uniform : FiniteEntropy.Law (RootLinkFeasibleState U A ell b q)).event (fun p=>P p.val.val) =
      (FiniteEntropy.uniform : FiniteEntropy.Law (FiniteNestedSubsets U b q)).event (fun p=>P p.val) := by
  let e : RootLinkFeasibleState U A ell b q ≃ FiniteNestedSubsets U b q :=
    ⟨(fun p=>p.val),(fun p=>⟨p,hall p⟩),(fun p=>rfl),(fun p=>rfl)⟩
  exact FiniteEntropy.Law.uniform_event_equiv e (fun p=>P p.val)

lemma root_link_star_condition_uniform (U A : SimpleHypergraph V) (ell : V → ℕ) (b q : ℕ)
    [Nonempty (RootLinkFeasibleState U A ell b q)] [Nonempty (FiniteNestedSubsets U b q)]
    (v : V) (hstar : ∀ p : FiniteNestedSubsets U b q,
      (∀w,ell w ≤ vertexDegree (A∪p.val.1) w) ↔ ¬Disjoint p.val.1 (rootLinkStar U v)) :
    ∃ hp : 0 < (FiniteEntropy.uniform : FiniteEntropy.Law (FiniteNestedSubsets U b q)).event
        (fun p=>¬Disjoint p.val.1 (rootLinkStar U v)),
      ∀ P : SimpleHypergraph V × SimpleHypergraph V → Prop,
      (FiniteEntropy.uniform : FiniteEntropy.Law (RootLinkFeasibleState U A ell b q)).event (fun p=>P p.val.val) =
        ((FiniteEntropy.uniform : FiniteEntropy.Law (FiniteNestedSubsets U b q)).condition
          (fun p=>¬Disjoint p.val.1 (rootLinkStar U v)) hp).event (fun p=>P p.val) := by
  let E : FiniteNestedSubsets U b q → Prop := fun p=>¬Disjoint p.val.1 (rootLinkStar U v)
  obtain ⟨w⟩ := ‹Nonempty (RootLinkFeasibleState U A ell b q)›
  have hw : E w.val := (hstar w.val).mp w.property
  letI : Nonempty {p : FiniteNestedSubsets U b q // E p} := ⟨⟨w.val,hw⟩⟩
  have hp : 0 < (FiniteEntropy.uniform : FiniteEntropy.Law (FiniteNestedSubsets U b q)).event E := by
    rw [FiniteEntropy.Law.uniform_event]
    apply div_pos
    · exact_mod_cast (card_pos.mpr ⟨w.val,mem_filter.mpr ⟨mem_univ _,hw⟩⟩)
    · exact_mod_cast Fintype.card_pos
  refine ⟨hp,?_⟩
  intro P
  let e : {p : FiniteNestedSubsets U b q // E p} ≃ RootLinkFeasibleState U A ell b q :=
    ⟨(fun p=>⟨p.val,(hstar p.val).mpr p.property⟩),
      (fun p=>⟨p.val,(hstar p.val).mp p.property⟩),(fun p=>rfl),(fun p=>rfl)⟩
  exact (uniform_conditioned_equiv E (fun p=>P p.val) e (fun p=>P p.val.val)
    (fun p=>Iff.rfl) hp).symm
end LooseHamilton
