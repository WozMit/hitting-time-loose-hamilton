module

public import HittingTimeLooseHamilton.EdgeComplementModels
public import HittingTimeLooseHamilton.BatchRemainderIdentities
public import HittingTimeLooseHamilton.UniformNestedOuter
public import HittingTimeLooseHamilton.UniformConditionalEquivalence

public section

/-! Reverse sampling inside a fixed allowed universe. The exposed terminal edges
remain in every original-vertex lower-degree constraint. -/
noncomputable section
namespace LooseHamilton
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
attribute [local instance] Classical.propDecidable

@[expose] def RestrictedBatchState (U A₀ : SimpleHypergraph V) (ell : V → ℕ) (s t τ : ℕ) :=
  {b : EdgeComplementPair U A₀ ell s t × SimpleHypergraph V //
    b.2 ⊆ b.1.val.2 ∧ b.2.card = τ}
@[expose] instance (U A₀ : SimpleHypergraph V) (ell : V → ℕ) (s t τ : ℕ) :
    Fintype (RestrictedBatchState U A₀ ell s t τ) := by
  unfold RestrictedBatchState; infer_instance

@[expose] def RestrictedReverseState (U A₀ F F₀ : SimpleHypergraph V) (ell : V → ℕ) (s τ : ℕ) :=
  {p : SimpleHypergraph V × SimpleHypergraph V //
    p.1 ⊆ p.2 ∧ p.2 ⊆ U \ F ∧ p.1.card = s - F₀.card ∧ p.2.card = τ ∧
    ∀ v, ell v ≤ vertexDegree (A₀ ∪ (F₀ ∪ p.1)) v}
@[expose] instance (U A₀ F F₀ : SimpleHypergraph V) (ell : V → ℕ) (s τ : ℕ) :
    Fintype (RestrictedReverseState U A₀ F F₀ ell s τ) := by
  unfold RestrictedReverseState; infer_instance

abbrev RestrictedReverseFiber (U A₀ F F₀ : SimpleHypergraph V)
    (ell : V → ℕ) (s t τ : ℕ) :=
  {b : RestrictedBatchState U A₀ ell s t τ //
    b.val.1.val.2 \ b.val.2 = F ∧ b.val.1.val.1 \ b.val.2 = F₀}

@[expose] def restrictedBatchToReverse (U A₀ F F₀ : SimpleHypergraph V)
    (ell : V → ℕ) (s t τ : ℕ) (b : RestrictedReverseFiber U A₀ F F₀ ell s t τ) :
    RestrictedReverseState U A₀ F F₀ ell s τ := by
  refine ⟨(b.val.val.2 ∩ b.val.val.1.val.1,b.val.val.2),inter_subset_left,?_,?_,
    b.val.property.2,?_⟩
  · intro e he
    exact mem_sdiff.mpr ⟨b.val.val.1.property.2.1 (b.val.property.1 he),by
      intro hef
      rw [←b.property.1] at hef
      exact (mem_sdiff.mp hef).2 he⟩
  · rw [batch_terminal_inter_card,b.val.val.1.property.2.2.1,b.property.2]
  · have he : F₀ ∪ (b.val.val.2 ∩ b.val.val.1.val.1) = b.val.val.1.val.1 := by
      simpa only [b.property.2] using batch_terminal_reconstruct b.val.val.1.val.1 b.val.val.2
    rw [he]
    exact b.val.val.1.property.2.2.2.2

lemma restrictedReverse_disjoint (U A₀ F F₀ : SimpleHypergraph V)
    (ell : V → ℕ) (s τ : ℕ) (p : RestrictedReverseState U A₀ F F₀ ell s τ) :
    Disjoint F p.val.2 := by
  apply disjoint_left.mpr
  intro e heF heT
  exact (mem_sdiff.mp (p.property.2.1 heT)).2 heF

end LooseHamilton
