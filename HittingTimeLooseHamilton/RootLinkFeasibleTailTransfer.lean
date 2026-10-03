module

public import HittingTimeLooseHamilton.RootLinkFiniteTail
public import HittingTimeLooseHamilton.UniformConditionalEquivalence

public section

noncomputable section
namespace LooseHamilton
open Finset
attribute [local instance] Classical.propDecidable
variable {A : Type*} [Fintype A] [DecidableEq A]

/-- Exact reduction of an arbitrary feasible nested family to no constraint or one star. -/
lemma uniform_feasible_zero_or_star_event_bound (U : Finset A) (b q : ℕ)
    (P E : FiniteNestedSubsets U b q → Prop) (γ : ℝ)
    [Nonempty {p : FiniteNestedSubsets U b q // P p}]
    [Nonempty (FiniteNestedSubsets U b q)]
    (hconstraint : (∀p,P p) ∨ ∃S⊆U,∀p,P p↔¬Disjoint p.val.1 S)
    (hall : (FiniteEntropy.uniform : FiniteEntropy.Law (FiniteNestedSubsets U b q)).event E≤γ)
    (hstar : ∀ (S : Finset A), S⊆U →
      ∀ hE : 0<(FiniteEntropy.uniform : FiniteEntropy.Law (FiniteNestedSubsets U b q)).event
        (fun p=>¬Disjoint p.val.1 S),
      ((FiniteEntropy.uniform : FiniteEntropy.Law (FiniteNestedSubsets U b q)).condition
        (fun p=>¬Disjoint p.val.1 S) hE).event E≤γ) :
    (FiniteEntropy.uniform : FiniteEntropy.Law {p : FiniteNestedSubsets U b q // P p}).event
      (fun p=>E p.val)≤γ := by
  rcases hconstraint with hallP | ⟨S,hS,hPS⟩
  · let e : {p : FiniteNestedSubsets U b q // P p} ≃ FiniteNestedSubsets U b q :=
      ⟨Subtype.val,(fun p=>⟨p,hallP p⟩),(fun _=>rfl),(fun _=>rfl)⟩
    have he := FiniteEntropy.Law.uniform_event_equiv e E
    exact he.trans_le hall
  · let H : FiniteNestedSubsets U b q→Prop := fun p=>¬Disjoint p.val.1 S
    obtain ⟨w⟩ := ‹Nonempty {p : FiniteNestedSubsets U b q // P p}›
    have hw : H w.val := (hPS w.val).mp w.property
    letI : Nonempty {p : FiniteNestedSubsets U b q // H p} := ⟨⟨w.val,hw⟩⟩
    have hp : 0<(FiniteEntropy.uniform : FiniteEntropy.Law (FiniteNestedSubsets U b q)).event H := by
      rw [FiniteEntropy.Law.uniform_event]
      apply div_pos
      · exact_mod_cast card_pos.mpr ⟨w.val,mem_filter.mpr ⟨mem_univ _,hw⟩⟩
      · exact_mod_cast Fintype.card_pos
    let e : {p : FiniteNestedSubsets U b q // H p} ≃ {p : FiniteNestedSubsets U b q // P p} :=
      ⟨(fun p=>⟨p.val,(hPS p.val).mpr p.property⟩),
       (fun p=>⟨p.val,(hPS p.val).mp p.property⟩),(fun _=>rfl),(fun _=>rfl)⟩
    have he := uniform_conditioned_equiv H E e (fun p=>E p.val) (fun _=>Iff.rfl) hp
    exact he.symm.trans_le (hstar S hS hp)
end LooseHamilton
