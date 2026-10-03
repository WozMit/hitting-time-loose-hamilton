module

public import HittingTimeLooseHamilton.RestrictedReverseEquiv
public import HittingTimeLooseHamilton.ExceptionalSetModels

public section

noncomputable section
namespace LooseHamilton
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
attribute [local instance] Classical.propDecidable

/-- No deficit is checked in the original terminal graph, including its fixed
exposed edges. No feasibility restriction on the reverse choices then remains. -/
@[expose] def restrictedReverseUnconstrainedEquiv (U A₀ F F₀ : SimpleHypergraph V)
    (ell : V → ℕ) (s τ : ℕ) (h₀ : ∀ v, ell v ≤ vertexDegree (A₀ ∪ F₀) v) :
    RestrictedReverseState U A₀ F F₀ ell s τ ≃
      FiniteNestedSubsets (U \ F) (s - F₀.card) τ where
  toFun p := ⟨p.val,p.property.1,p.property.2.2.1,
    mem_powersetCard.mpr ⟨p.property.2.1,p.property.2.2.2.1⟩⟩
  invFun p := ⟨p.val,p.property.1,(mem_powersetCard.mp p.property.2.2).1,
    p.property.2.1,(mem_powersetCard.mp p.property.2.2).2,
    fun v => (h₀ v).trans (vertexDegree_mono (union_subset_union_right subset_union_left) v)⟩
  left_inv _ := rfl
  right_inv _ := rfl

lemma restrictedReverse_outer_nonempty (U A₀ F F₀ : SimpleHypergraph V)
    (ell : V → ℕ) (s τ : ℕ) [Nonempty (RestrictedReverseState U A₀ F F₀ ell s τ)] :
    Nonempty ↥((U \ F).powersetCard τ) := by
  obtain ⟨p⟩ := ‹Nonempty (RestrictedReverseState U A₀ F F₀ ell s τ)›
  exact ⟨⟨p.val.2,mem_powersetCard.mpr ⟨p.property.2.1,p.property.2.2.2.1⟩⟩⟩

theorem restrictedReverse_outer_uniform_event (U A₀ F F₀ : SimpleHypergraph V)
    (ell : V → ℕ) (s τ : ℕ) [Nonempty (RestrictedReverseState U A₀ F F₀ ell s τ)]
    (h₀ : ∀ v, ell v ≤ vertexDegree (A₀ ∪ F₀) v) (P : SimpleHypergraph V → Prop) :
    (FiniteEntropy.uniform : FiniteEntropy.Law (RestrictedReverseState U A₀ F F₀ ell s τ)).event
      (fun p => P p.val.2) =
    (@FiniteEntropy.uniform ↥((U \ F).powersetCard τ) inferInstance
      (restrictedReverse_outer_nonempty U A₀ F F₀ ell s τ)).event (fun T => P T.val) := by
  letI := restrictedReverse_outer_nonempty U A₀ F F₀ ell s τ
  let e := restrictedReverseUnconstrainedEquiv U A₀ F F₀ ell s τ h₀
  letI : Nonempty (FiniteNestedSubsets (U \ F) (s-F₀.card) τ) := by
    obtain ⟨p⟩ := ‹Nonempty (RestrictedReverseState U A₀ F F₀ ell s τ)›
    exact ⟨e p⟩
  have he := FiniteEntropy.Law.uniform_event_equiv e
    (fun p : FiniteNestedSubsets (U \ F) (s-F₀.card) τ => P p.val.2)
  change (FiniteEntropy.uniform : FiniteEntropy.Law (RestrictedReverseState U A₀ F F₀ ell s τ)).event
    (fun p => P p.val.2) = _ at he
  rw [he]
  have hh := congrArg (fun p : FiniteEntropy.Law ↥((U \ F).powersetCard τ) =>
    p.event (fun T => P T.val)) (uniform_nested_outer (U \ F) (s-F₀.card) τ)
  simpa only [FiniteEntropy.Law.event_map,nestedOuter] using hh

/-- Exact pair law after observing both remainders. Positive probability is the
only consistency assumption on this observation. -/
theorem restrictedReverse_pair_law (U A₀ F F₀ : SimpleHypergraph V)
    (ell : V → ℕ) (s t τ : ℕ) [Nonempty (RestrictedBatchState U A₀ ell s t τ)]
    (hE : 0 < (FiniteEntropy.uniform : FiniteEntropy.Law (RestrictedBatchState U A₀ ell s t τ)).event
      (fun b => b.val.1.val.2 \ b.val.2 = F ∧ b.val.1.val.1 \ b.val.2 = F₀)) :
    ∃ hR : Nonempty (RestrictedReverseState U A₀ F F₀ ell s τ),
    ∀ P : SimpleHypergraph V × SimpleHypergraph V → Prop,
    ((FiniteEntropy.uniform : FiniteEntropy.Law (RestrictedBatchState U A₀ ell s t τ)).condition
      (fun b => b.val.1.val.2 \ b.val.2 = F ∧ b.val.1.val.1 \ b.val.2 = F₀) hE).event
      (fun b => P (b.val.2 ∩ b.val.1.val.1,b.val.2)) =
    (@FiniteEntropy.uniform (RestrictedReverseState U A₀ F F₀ ell s τ) inferInstance hR).event
      (fun p => P p.val) := by
  obtain ⟨b,hb⟩ := exists_of_event_pos _ _ hE
  let W : RestrictedReverseFiber U A₀ F F₀ ell s t τ := ⟨b,hb⟩
  let e := restrictedReverseEquiv U A₀ F F₀ ell s t τ W
  letI : Nonempty (RestrictedReverseFiber U A₀ F F₀ ell s t τ) := ⟨W⟩
  letI : Nonempty (RestrictedReverseState U A₀ F F₀ ell s τ) := ⟨e W⟩
  refine ⟨inferInstance,fun P => ?_⟩
  exact uniform_conditioned_equiv _ _ e (fun p => P p.val) (fun _ => Iff.rfl) hE

end LooseHamilton
