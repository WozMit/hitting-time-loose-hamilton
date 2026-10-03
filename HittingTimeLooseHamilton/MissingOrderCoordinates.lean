module

public import HittingTimeLooseHamilton.ExtensionSubsetKernel

public section

/-! Finite-order coordinates for a fixed terminal graph's missing-edge extension. -/
noncomputable section
namespace LooseHamilton
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V] {r M : ℕ} {ell : V → ℕ}

@[expose] def missingFiniteOrderEquiv (F : TerminalState V r M ell) :
    MissingOrder V r M ≃ FiniteOrder (MissingEdge F) :=
  (missingOrderEquiv F).trans (Equiv.equivCongr (Equiv.refl _) (finCongr (missing_card F).symm))

@[simp] lemma missingFiniteOrder_rank (F : TerminalState V r M ell)
    (σ : MissingOrder V r M) (e : MissingEdge F) :
    (missingFiniteOrderEquiv F σ e).val = (missingOrder F σ e).val := rfl

@[expose] def liftMissing (F : TerminalState V r M ell) (H : SimpleHypergraph V) : Finset (MissingEdge F) :=
  univ.filter (fun e => e.val ∈ H)

@[simp] lemma mem_liftMissing (F : TerminalState V r M ell) (H : SimpleHypergraph V) (e : MissingEdge F) :
    e ∈ liftMissing F H ↔ e.val ∈ H := by simp [liftMissing]

lemma liftMissing_image (F : TerminalState V r M ell) (H : SimpleHypergraph V)
    (hH : H ⊆ completeEdges V r) : (liftMissing F H).image Subtype.val = H \ F.val := by
  ext e
  simp only [mem_image,mem_liftMissing,mem_sdiff]
  constructor
  · rintro ⟨a,ha,rfl⟩
    exact ⟨ha,(mem_sdiff.mp a.property).2⟩
  · rintro ⟨he,hn⟩
    exact ⟨⟨e,mem_sdiff.mpr ⟨hH he,hn⟩⟩,he,rfl⟩

lemma liftMissing_card (F : TerminalState V r M ell) (H : SimpleHypergraph V)
    (hH : H ⊆ completeEdges V r) (hF : F.val ⊆ H) :
    (liftMissing F H).card = H.card-M := by
  rw [←card_image_of_injective _ Subtype.val_injective,liftMissing_image F H hH,
    card_sdiff_of_subset hF,F.property.2.1]

lemma mem_extensionState_missing (F : TerminalState V r M ell) (σ : MissingOrder V r M)
    (j : ℕ) (e : MissingEdge F) :
    e.val ∈ extensionState F σ j ↔ (missingOrder F σ e).val < j-M := by
  have heF := (mem_sdiff.mp e.property).2
  simp only [extensionState,mem_union,heF,false_or,mem_image,mem_filter,mem_univ,true_and]
  constructor
  · rintro ⟨a,ha,he⟩
    have : a=e := Subtype.ext he
    simpa [this] using ha
  · intro h
    exact ⟨e,h,rfl⟩

lemma extensionState_eq_iff_missing_prefix (F : TerminalState V r M ell)
    (σ : MissingOrder V r M) (j : ℕ) (H : SimpleHypergraph V)
    (hH : H ⊆ completeEdges V r) (hF : F.val ⊆ H) :
    extensionState F σ j = H ↔ orderPrefix (missingFiniteOrderEquiv F σ) (j-M) = liftMissing F H := by
  constructor
  · intro h
    ext e
    rw [mem_orderPrefix,missingFiniteOrder_rank,←mem_extensionState_missing,h,mem_liftMissing]
  · intro h
    apply Finset.Subset.antisymm
    · intro e he
      by_cases heF : e∈F.val
      · exact hF heF
      · let a : MissingEdge F := ⟨e,mem_sdiff.mpr ⟨extensionState_subset F σ j he,heF⟩⟩
        have ha : a∈orderPrefix (missingFiniteOrderEquiv F σ) (j-M) :=
          by simpa only [mem_orderPrefix,missingFiniteOrder_rank] using (mem_extensionState_missing F σ j a).mp he
        rw [h,mem_liftMissing] at ha
        exact ha
    · intro e he
      by_cases heF : e∈F.val
      · exact mem_union_left _ heF
      · let a : MissingEdge F := ⟨e,mem_sdiff.mpr ⟨hH he,heF⟩⟩
        have ha : a∈liftMissing F H := (mem_liftMissing F H a).mpr he
        rw [←h] at ha
        exact (mem_extensionState_missing F σ j a).mpr (by simpa only [mem_orderPrefix,missingFiniteOrder_rank] using ha)
end LooseHamilton
