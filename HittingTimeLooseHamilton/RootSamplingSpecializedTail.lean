module

public import HittingTimeLooseHamilton.RootLinkConditionalReduction
public import HittingTimeLooseHamilton.RootLinkFeasibleTail

public section

noncomputable section
namespace LooseHamilton
open Finset
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] [DecidableEq V]

lemma root_link_arbitrary_star_condition_uniform (U A S : SimpleHypergraph V)
    (ell : V→ℕ) (b q : ℕ)
    [Nonempty (RootLinkFeasibleState U A ell b q)] [Nonempty (FiniteNestedSubsets U b q)]
    (hstar : ∀p : FiniteNestedSubsets U b q,
      (∀w,ell w≤vertexDegree (A∪p.val.1) w) ↔ ¬Disjoint p.val.1 S) :
    ∃ hp : 0<(FiniteEntropy.uniform : FiniteEntropy.Law (FiniteNestedSubsets U b q)).event
        (fun p=>¬Disjoint p.val.1 S),
      ∀ P : SimpleHypergraph V × SimpleHypergraph V→Prop,
      (FiniteEntropy.uniform : FiniteEntropy.Law (RootLinkFeasibleState U A ell b q)).event (fun p=>P p.val.val)=
        ((FiniteEntropy.uniform : FiniteEntropy.Law (FiniteNestedSubsets U b q)).condition
          (fun p=>¬Disjoint p.val.1 S) hp).event (fun p=>P p.val) := by
  let E : FiniteNestedSubsets U b q→Prop := fun p=>¬Disjoint p.val.1 S
  obtain ⟨w⟩ := ‹Nonempty (RootLinkFeasibleState U A ell b q)›
  have hw : E w.val := (hstar w.val).mp w.property
  letI : Nonempty {p : FiniteNestedSubsets U b q // E p} := ⟨⟨w.val,hw⟩⟩
  have hp : 0<(FiniteEntropy.uniform : FiniteEntropy.Law (FiniteNestedSubsets U b q)).event E := by
    rw [FiniteEntropy.Law.uniform_event]
    apply div_pos
    · exact_mod_cast card_pos.mpr ⟨w.val,mem_filter.mpr ⟨mem_univ _,hw⟩⟩
    · exact_mod_cast Fintype.card_pos
  refine ⟨hp,?_⟩
  intro P
  let e : {p : FiniteNestedSubsets U b q // E p} ≃ RootLinkFeasibleState U A ell b q :=
    ⟨(fun p=>⟨p.val,(hstar p.val).mpr p.property⟩),
      (fun p=>⟨p.val,(hstar p.val).mp p.property⟩),(fun p=>rfl),(fun p=>rfl)⟩
  exact (uniform_conditioned_equiv E (fun p=>P p.val) e (fun p=>P p.val.val)
    (fun p=>Iff.rfl) hp).symm

/-- Specialized bridge preserving the concrete feasible-state instances throughout. -/
theorem root_link_feasible_tail (U A Γ R : SimpleHypergraph V) (ell : V→ℕ)
    (b q Q h : ℕ) (ρ : ℝ) [Nonempty (RootLinkFeasibleState U A ell b q)]
    (hqU : q≤U.card) (hU : 0<U.card) (hqQ : q≤Q) (hQ : 12*(h+1)≤Q) (hR : R.card≤h)
    (hρ : 0≤ρ) (hsmall : 8*ρ≤1) (hden : ((Γ∩U).card:ℝ)/U.card≤2*ρ)
    (hconstraint : (∀p : FiniteNestedSubsets U b q,∀v,ell v≤vertexDegree (A∪p.val.1) v) ∨
      ∃S⊆U,∀p : FiniteNestedSubsets U b q,
        (∀v,ell v≤vertexDegree (A∪p.val.1) v)↔¬Disjoint p.val.1 S) :
    (FiniteEntropy.uniform : FiniteEntropy.Law (RootLinkFeasibleState U A ell b q)).event
      (fun B=>2*Q≤3*((B.val.val.2∪R)∩Γ).card)≤(8*ρ)^((Q:ℝ)/4) := by
  letI := root_link_feasible_nonempty_nested U A ell b q
  obtain ⟨w⟩ := ‹Nonempty (RootLinkFeasibleState U A ell b q)›
  have hbq : b≤q := by
    have hh := card_le_card w.val.property.1
    rw [w.val.property.2.1,(mem_powersetCard.mp w.val.property.2.2).2] at hh
    exact hh
  let E : SimpleHypergraph V × SimpleHypergraph V→Prop := fun B=>2*Q≤3*((B.2∪R)∩Γ).card
  rcases hconstraint with hall|⟨S,hS,hstar⟩
  · have he := root_link_unrestricted_uniform U A ell b q hall E
    apply he.trans_le
    exact uniform_nested_prescribed_root_tail U Γ R b q Q h ρ hqU hU hqQ hQ hR hρ hsmall hden
  · obtain ⟨hp,he⟩ := root_link_arbitrary_star_condition_uniform U A S ell b q hstar
    apply (he E).trans_le
    exact conditioned_nested_prescribed_root_tail U Γ R S b q Q h ρ hS hbq hqU hU
      hqQ hQ hR hρ hsmall hden hp
end LooseHamilton
