module

public import HittingTimeLooseHamilton.NestedPairLaw

public section

/-! A genuine independent uniform batch selected from the current graph under Q. -/
noncomputable section
namespace LooseHamilton
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A feasible terminal/current pair together with a tau-edge subset of its current host. -/
@[expose] def BatchState (V : Type*) [Fintype V] [DecidableEq V]
    (r M : ℕ) (ell : V → ℕ) (m τ : ℕ) :=
  {p : NestedState V r M ell m × SimpleHypergraph V // p.2 ⊆ p.1.val.2 ∧ p.2.card=τ}

@[expose] instance (r M : ℕ) (ell : V → ℕ) (m τ : ℕ) : Fintype (BatchState V r M ell m τ) := by
  classical
  unfold BatchState
  infer_instance
@[expose] instance (r M : ℕ) (ell : V → ℕ) (m τ : ℕ) : DecidableEq (BatchState V r M ell m τ) :=
  Classical.decEq _

abbrev BatchOrder (m : ℕ) := Equiv.Perm (Fin m)

/-- Independent order coordinates of a fixed m-edge host. -/
@[expose] def batchOrderEquiv (H : SimpleHypergraph V) (m : ℕ) (hH : H.card=m) :
    BatchOrder m ≃ FiniteOrder ↥H :=
  Equiv.equivCongr (Fintype.equivFinOfCardEq (by simpa using hH) : ↥H ≃ Fin m).symm
    (finCongr (show m=Fintype.card ↥H by simpa using hH.symm))

@[expose] def batchSelection (H : SimpleHypergraph V) (m : ℕ) (hH : H.card=m)
    (τ : ℕ) (σ : BatchOrder m) : SimpleHypergraph V :=
  (orderPrefix (batchOrderEquiv H m hH σ) τ).image Subtype.val

omit [Fintype V] in
lemma batchSelection_subset (H : SimpleHypergraph V) (m : ℕ) (hH : H.card=m)
    (τ : ℕ) (σ : BatchOrder m) : batchSelection H m hH τ σ ⊆ H := by
  intro e he
  obtain ⟨a,ha,rfl⟩ := mem_image.mp he
  exact a.property

lemma batchSelection_card (H : SimpleHypergraph V) (m : ℕ) (hH : H.card=m)
    (τ : ℕ) (hτ : τ ≤ m) (σ : BatchOrder m) : (batchSelection H m hH τ σ).card=τ := by
  rw [batchSelection,card_image_of_injective _ Subtype.val_injective,orderPrefix_card]
  simpa only [Fintype.card_coe,hH] using hτ

/-- Source law: first sample the genuine Q path, then an independent uniform permutation of m positions. -/
@[expose] def batchLaw (r M : ℕ) (ell : V → ℕ) [Nonempty (TerminalState V r M ell)] (m : ℕ) :
    FiniteEntropy.Law ((TerminalState V r M ell × MissingOrder V r M) × BatchOrder m) :=
  (extensionLaw r M ell).prod FiniteEntropy.uniform

@[expose] def nestedBatchState (r M : ℕ) (ell : V → ℕ) (m τ : ℕ) (hτ : τ ≤ m)
    (p : NestedState V r M ell m) (σ : BatchOrder m) : BatchState V r M ell m τ :=
  ⟨⟨p,batchSelection p.val.2 m p.property.2.2 τ σ⟩,
    batchSelection_subset _ _ _ _ _,batchSelection_card _ _ _ _ hτ _⟩

@[expose] def observedBatchState (r M : ℕ) (ell : V → ℕ) (m τ : ℕ)
    (hMm : M ≤ m) (hm : m ≤ (completeEdges V r).card) (hτ : τ ≤ m)
    (ω : (TerminalState V r M ell × MissingOrder V r M) × BatchOrder m) : BatchState V r M ell m τ :=
  nestedBatchState r M ell m τ hτ (extensionNestedState r M ell m hMm hm ω.1) ω.2

lemma batchState_nonempty (r M : ℕ) (ell : V → ℕ) [Nonempty (TerminalState V r M ell)]
    (m τ : ℕ) (hMm : M ≤ m) (hm : m ≤ (completeEdges V r).card) (hτ : τ ≤ m) :
    Nonempty (BatchState V r M ell m τ) := by
  obtain ⟨p⟩ := nestedState_nonempty r M ell m hMm hm
  exact ⟨nestedBatchState r M ell m τ hτ p (Equiv.refl _)⟩
end LooseHamilton
