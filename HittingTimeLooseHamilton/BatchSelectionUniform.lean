module

public import HittingTimeLooseHamilton.BatchModels

public section

/-! A fresh uniform order selects a uniform tau-subset of the entire current host. -/
noncomputable section
namespace LooseHamilton
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

lemma batchSelection_probability (H : SimpleHypergraph V) (m : ℕ) (hH : H.card=m)
    (τ : ℕ) (hτ : τ ≤ m) (T : SimpleHypergraph V) (hT : T ⊆ H) (hTc : T.card=τ) :
    (FiniteEntropy.uniform : FiniteEntropy.Law (BatchOrder m)).event
      (fun σ => batchSelection H m hH τ σ=T) = 1/(m.choose τ:ℝ) := by
  classical
  let S : Finset ↥H := univ.filter (fun e => e.val∈T)
  have himage : S.image Subtype.val=T := by
    ext e
    simp only [S,mem_image,mem_filter,mem_univ,true_and]
    constructor
    · rintro ⟨a,ha,rfl⟩
      exact ha
    · intro he
      exact ⟨⟨e,hT he⟩,he,rfl⟩
  have hSc : S.card=τ := by
    rw [←card_image_of_injective _ Subtype.val_injective,himage,hTc]
  have hprefix (σ : BatchOrder m) : batchSelection H m hH τ σ=T ↔
      orderPrefix (batchOrderEquiv H m hH σ) τ=S := by
    rw [batchSelection,←himage,image_inj Subtype.val_injective]
  simp_rw [hprefix]
  rw [FiniteEntropy.Law.uniform_event_equiv (batchOrderEquiv H m hH) (fun σ => orderPrefix σ τ=S),FiniteEntropy.Law.uniform_event]
  have hp := uniform_order_prefix_probability τ (by simpa [hH] using hτ) S hSc
  simpa only [Fintype.card_coe,hH] using hp

lemma nestedBatchState_eq_iff (r M : ℕ) (ell : V → ℕ) (m τ : ℕ) (hτ : τ ≤ m)
    (p : NestedState V r M ell m) (σ : BatchOrder m) (b : BatchState V r M ell m τ) :
    nestedBatchState r M ell m τ hτ p σ=b ↔
      p=b.val.1 ∧ batchSelection p.val.2 m p.property.2.2 τ σ=b.val.2 := by
  constructor
  · intro h
    have hv := congrArg Subtype.val h
    exact ⟨congrArg Prod.fst hv, congrArg Prod.snd hv⟩
  · rintro ⟨hp, hS⟩
    apply Subtype.ext
    exact Prod.ext hp hS

lemma nestedBatchState_probability (r M : ℕ) (ell : V → ℕ) (m τ : ℕ) (hτ : τ ≤ m)
    (p : NestedState V r M ell m) (b : BatchState V r M ell m τ) :
    (FiniteEntropy.uniform : FiniteEntropy.Law (BatchOrder m)).event
      (fun σ => nestedBatchState r M ell m τ hτ p σ=b) =
        if p=b.val.1 then 1/(m.choose τ:ℝ) else 0 := by
  classical
  simp_rw [nestedBatchState_eq_iff]
  rw [FiniteEntropy.Law.event_const_and]
  split_ifs with hp
  · subst p
    exact batchSelection_probability b.val.1.val.2 m b.val.1.property.2.2 τ hτ b.val.2
      b.property.1 b.property.2
  · rfl
end LooseHamilton
