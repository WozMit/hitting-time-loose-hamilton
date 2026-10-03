module

public import HittingTimeLooseHamilton.BatchSelectionUniform
public import HittingTimeLooseHamilton.FrameSurvivalCounting

public section

/-! The independent-order batch used in item 30.5 and actual Q resampling has
the same law as the uniform host-subset batch used in item 30.6. -/
noncomputable section
namespace LooseHamilton
open Finset FrameSurvival
variable {V : Type*} [Fintype V] [DecidableEq V]

@[expose] def selectedHostBatch (H : SimpleHypergraph V) (τ : ℕ) (hτ : τ ≤ H.card)
    (σ : BatchOrder H.card) : HostBatch H τ :=
  ⟨batchSelection H H.card rfl τ σ,
    mem_powersetCard.mpr ⟨batchSelection_subset _ _ _ _ _, batchSelection_card _ _ _ _ hτ _⟩⟩

/-- Equality of laws transfers every event and moment, not just individual atoms. -/
theorem selectedHostBatch_uniform (H : SimpleHypergraph V) (τ : ℕ) (hτ : τ ≤ H.card) :
    (FiniteEntropy.uniform : FiniteEntropy.Law (BatchOrder H.card)).map
      (selectedHostBatch H τ hτ) = hostBatchLaw hτ := by
  classical
  apply FiniteEntropy.Law.ext_mass
  intro T
  change (FiniteEntropy.uniform : FiniteEntropy.Law (BatchOrder H.card)).event
    (fun σ => selectedHostBatch H τ hτ σ = T) = _
  have he : (fun σ => selectedHostBatch H τ hτ σ = T) =
      (fun σ => batchSelection H H.card rfl τ σ = T.val) := by
    funext σ
    exact propext Subtype.ext_iff
  rw [he, batchSelection_probability H H.card rfl τ hτ T.val
    (mem_powersetCard.mp T.property).1 (mem_powersetCard.mp T.property).2]
  simp [hostBatchLaw, FiniteEntropy.uniform, Fintype.card_coe, card_powersetCard, one_div]

theorem selectedHostBatch_event (H : SimpleHypergraph V) (τ : ℕ) (hτ : τ ≤ H.card)
    (P : SimpleHypergraph V → Prop) :
    (FiniteEntropy.uniform : FiniteEntropy.Law (BatchOrder H.card)).event
      (fun σ => P (batchSelection H H.card rfl τ σ)) =
      (hostBatchLaw hτ).event (fun T => P T.val) := by
  have h := congrArg (fun p : FiniteEntropy.Law (HostBatch H τ) => p.event (fun T => P T.val))
    (selectedHostBatch_uniform H τ hτ)
  simpa only [FiniteEntropy.Law.event_map, selectedHostBatch] using h

end LooseHamilton
