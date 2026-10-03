module

public import HittingTimeLooseHamilton.RestrictedReverseUniform

public section

noncomputable section
namespace LooseHamilton
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
attribute [local instance] Classical.propDecidable

/-- Transfer the exact reverse pair law to any source experiment whose observed
restricted triple is uniform, in particular the exposed Q experiment with an
independent uniform batch. -/
theorem restrictedReverse_pair_law_of_uniform_pushforward
    (U A₀ F F₀ : SimpleHypergraph V) (ell : V → ℕ) (s t τ : ℕ)
    [Nonempty (RestrictedBatchState U A₀ ell s t τ)]
    {Ω : Type*} [Fintype Ω] (p : FiniteEntropy.Law Ω)
    (f : Ω → RestrictedBatchState U A₀ ell s t τ)
    (hf : p.map f = FiniteEntropy.uniform)
    (hE : 0 < p.event (fun ω =>
      (f ω).val.1.val.2 \ (f ω).val.2 = F ∧
      (f ω).val.1.val.1 \ (f ω).val.2 = F₀)) :
    ∃ hR : Nonempty (RestrictedReverseState U A₀ F F₀ ell s τ),
    ∀ P : SimpleHypergraph V × SimpleHypergraph V → Prop,
    (p.condition (fun ω =>
      (f ω).val.1.val.2 \ (f ω).val.2 = F ∧
      (f ω).val.1.val.1 \ (f ω).val.2 = F₀) hE).event
      (fun ω => P ((f ω).val.2 ∩ (f ω).val.1.val.1,(f ω).val.2)) =
    (@FiniteEntropy.uniform (RestrictedReverseState U A₀ F F₀ ell s τ) inferInstance hR).event
      (fun q => P q.val) := by
  obtain ⟨ω,hω⟩ := exists_of_event_pos _ _ hE
  let W : RestrictedReverseFiber U A₀ F F₀ ell s t τ := ⟨f ω,hω⟩
  let e := restrictedReverseEquiv U A₀ F F₀ ell s t τ W
  letI : Nonempty (RestrictedReverseFiber U A₀ F F₀ ell s t τ) := ⟨W⟩
  letI : Nonempty (RestrictedReverseState U A₀ F F₀ ell s τ) := ⟨e W⟩
  refine ⟨inferInstance,fun P => ?_⟩
  exact uniform_pushforward_conditioned_equiv p f hf
    (fun b => b.val.1.val.2 \ b.val.2 = F ∧ b.val.1.val.1 \ b.val.2 = F₀)
    (fun b => P (b.val.2 ∩ b.val.1.val.1,b.val.2)) e
    (fun q => P q.val) (fun _ => Iff.rfl) hE

/-- With no original terminal deficit, the removed current batch is exactly a
uniform tau-subset of the unexposed universe minus the current remainder. -/
theorem restrictedReverse_batch_law_of_uniform_pushforward
    (U A₀ F F₀ : SimpleHypergraph V) (ell : V → ℕ) (s t τ : ℕ)
    [Nonempty (RestrictedBatchState U A₀ ell s t τ)]
    {Ω : Type*} [Fintype Ω] (p : FiniteEntropy.Law Ω)
    (f : Ω → RestrictedBatchState U A₀ ell s t τ)
    (hf : p.map f = FiniteEntropy.uniform)
    (h₀ : ∀ v, ell v ≤ vertexDegree (A₀ ∪ F₀) v)
    (hE : 0 < p.event (fun ω =>
      (f ω).val.1.val.2 \ (f ω).val.2 = F ∧
      (f ω).val.1.val.1 \ (f ω).val.2 = F₀)) :
    ∃ hT : Nonempty ↥((U \ F).powersetCard τ),
    ∀ P : SimpleHypergraph V → Prop,
    (p.condition (fun ω =>
      (f ω).val.1.val.2 \ (f ω).val.2 = F ∧
      (f ω).val.1.val.1 \ (f ω).val.2 = F₀) hE).event
      (fun ω => P (f ω).val.2) =
    (@FiniteEntropy.uniform ↥((U \ F).powersetCard τ) inferInstance hT).event
      (fun T => P T.val) := by
  obtain ⟨hR,hpair⟩ := restrictedReverse_pair_law_of_uniform_pushforward
    U A₀ F F₀ ell s t τ p f hf hE
  letI := hR
  refine ⟨restrictedReverse_outer_nonempty U A₀ F F₀ ell s τ,fun P => ?_⟩
  exact (hpair (fun q => P q.2)).trans
    (restrictedReverse_outer_uniform_event U A₀ F F₀ ell s τ h₀ P)
end LooseHamilton
