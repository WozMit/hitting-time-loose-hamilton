module

public import HittingTimeLooseHamilton.RestrictedReverseModels

public section

noncomputable section
namespace LooseHamilton
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

@[expose] def restrictedReverseToBatch (U A₀ F F₀ : SimpleHypergraph V)
    (ell : V → ℕ) (s t τ : ℕ) (W : RestrictedReverseFiber U A₀ F F₀ ell s t τ)
    (p : RestrictedReverseState U A₀ F F₀ ell s τ) :
    RestrictedReverseFiber U A₀ F F₀ ell s t τ := by
  have hF₀F : F₀ ⊆ F := by
    simpa only [W.property.1,W.property.2] using
      sdiff_subset_sdiff W.val.val.1.property.1 (Subset.refl W.val.val.2)
  have hFu : F ⊆ U := by
    simpa only [W.property.1] using
      (sdiff_subset.trans W.val.val.1.property.2.1 : W.val.val.1.val.2 \ W.val.val.2 ⊆ U)
  have hF₀s : F₀.card ≤ s := by
    have h := card_le_card (sdiff_subset : W.val.val.1.val.1 \ W.val.val.2 ⊆ W.val.val.1.val.1)
    simpa only [W.property.2,W.val.val.1.property.2.2.1] using h
  have hτt : τ ≤ t := by
    simpa only [W.val.property.2,W.val.val.1.property.2.2.2.1] using
      card_le_card W.val.property.1
  have hFc : F.card = t - τ := by
    have h := card_sdiff_of_subset W.val.property.1
    simpa only [W.property.1,W.val.val.1.property.2.2.2.1,W.val.property.2] using h
  have hd := restrictedReverse_disjoint U A₀ F F₀ ell s τ p
  have hd₀ := hd.mono_left hF₀F
  have hd₀₀ := hd₀.mono_right p.property.1
  have hTu : p.val.2 ⊆ U := p.property.2.1.trans sdiff_subset
  have hSc : (F₀ ∪ p.val.1).card = s := by
    rw [card_union_of_disjoint hd₀₀,p.property.2.2.1]; omega
  have hHc : (F ∪ p.val.2).card = t := by
    rw [card_union_of_disjoint hd,hFc,p.property.2.2.2.1]; omega
  let q : EdgeComplementPair U A₀ ell s t :=
    ⟨(F₀ ∪ p.val.1,F ∪ p.val.2),union_subset_union hF₀F p.property.1,
      union_subset hFu hTu,hSc,hHc,p.property.2.2.2.2⟩
  let b : RestrictedBatchState U A₀ ell s t τ :=
    ⟨(q,p.val.2),subset_union_right,p.property.2.2.2.1⟩
  exact ⟨b,union_sdiff_cancel_right hd,batch_restore_terminal_remainder hd₀ p.property.1⟩

/-- A positive observation imposes exactly the two residual sizes, containment in
U minus F, and the original lower-degree feasibility with exposed edges A₀. -/
@[expose] def restrictedReverseEquiv (U A₀ F F₀ : SimpleHypergraph V)
    (ell : V → ℕ) (s t τ : ℕ) (W : RestrictedReverseFiber U A₀ F F₀ ell s t τ) :
    RestrictedReverseFiber U A₀ F F₀ ell s t τ ≃
      RestrictedReverseState U A₀ F F₀ ell s τ where
  toFun := restrictedBatchToReverse U A₀ F F₀ ell s t τ
  invFun := restrictedReverseToBatch U A₀ F F₀ ell s t τ W
  left_inv b := by
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · apply Subtype.ext
      apply Prod.ext
      · change F₀ ∪ (b.val.val.2 ∩ b.val.val.1.val.1) = b.val.val.1.val.1
        simpa only [b.property.2] using batch_terminal_reconstruct b.val.val.1.val.1 b.val.val.2
      · change F ∪ b.val.val.2 = b.val.val.1.val.2
        simpa only [b.property.1] using sdiff_union_of_subset b.val.property.1
    · rfl
  right_inv p := by
    have hF₀F : F₀ ⊆ F := by
      simpa only [W.property.1,W.property.2] using
        sdiff_subset_sdiff W.val.val.1.property.1 (Subset.refl W.val.val.2)
    have hd := (restrictedReverse_disjoint U A₀ F F₀ ell s τ p).mono_left hF₀F
    apply Subtype.ext
    apply Prod.ext
    · change p.val.2 ∩ (F₀ ∪ p.val.1) = p.val.1
      exact batch_restore_terminal_inter hd p.property.1
    · rfl

end LooseHamilton
