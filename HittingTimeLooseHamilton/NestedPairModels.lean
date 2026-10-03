module

public import HittingTimeLooseHamilton.Models

public section

/-! Genuine nested terminal/current graph pairs at a fixed extension time. -/
noncomputable section
namespace LooseHamilton
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A terminal-feasible M-edge graph together with a j-edge host containing it. -/
@[expose] def NestedState (V : Type*) [Fintype V] [DecidableEq V] (r M : ℕ) (ell : V → ℕ) (j : ℕ) :=
  {p : TerminalState V r M ell × SimpleHypergraph V //
    p.1.val ⊆ p.2 ∧ p.2 ⊆ completeEdges V r ∧ p.2.card=j}

@[expose] instance (r M : ℕ) (ell : V → ℕ) (j : ℕ) : Fintype (NestedState V r M ell j) := by
  classical
  unfold NestedState
  infer_instance

@[expose] instance (r M : ℕ) (ell : V → ℕ) (j : ℕ) : DecidableEq (NestedState V r M ell j) :=
  Classical.decEq _

@[expose] def extensionNestedState (r M : ℕ) (ell : V → ℕ) (j : ℕ)
    (hMj : M ≤ j) (hj : j ≤ (completeEdges V r).card)
    (ω : TerminalState V r M ell × MissingOrder V r M) : NestedState V r M ell j :=
  ⟨⟨ω.1,extensionState ω.1 ω.2 j⟩,Finset.subset_union_left,
    extensionState_subset ω.1 ω.2 j,extensionState_card ω.1 ω.2 j hMj hj⟩

@[expose] instance nestedStateNonempty (r M : ℕ) (ell : V → ℕ) (j : ℕ)
    [Nonempty (TerminalState V r M ell)] [Fact (M ≤ j)] [Fact (j ≤ (completeEdges V r).card)] :
    Nonempty (NestedState V r M ell j) := by
  obtain ⟨F⟩ := ‹Nonempty (TerminalState V r M ell)›
  exact ⟨extensionNestedState r M ell j Fact.out Fact.out (F,Equiv.refl _)⟩

lemma nestedState_nonempty (r M : ℕ) (ell : V → ℕ) (j : ℕ)
    [Nonempty (TerminalState V r M ell)] (hMj : M ≤ j) (hj : j ≤ (completeEdges V r).card) :
    Nonempty (NestedState V r M ell j) := by
  letI : Fact (M ≤ j) := ⟨hMj⟩
  letI : Fact (j ≤ (completeEdges V r).card) := ⟨hj⟩
  infer_instance

lemma extensionNestedState_eq_iff (r M : ℕ) (ell : V → ℕ) (j : ℕ)
    (hMj : M ≤ j) (hj : j ≤ (completeEdges V r).card)
    (ω : TerminalState V r M ell × MissingOrder V r M) (p : NestedState V r M ell j) :
    extensionNestedState r M ell j hMj hj ω=p ↔
      ω.1=p.val.1 ∧ extensionState ω.1 ω.2 j=p.val.2 := by
  constructor
  · intro h
    have he := congrArg Subtype.val h
    exact ⟨congrArg Prod.fst he, congrArg Prod.snd he⟩
  · rintro ⟨h₁,h₂⟩
    exact Subtype.ext (Prod.ext h₁ h₂)
end LooseHamilton
