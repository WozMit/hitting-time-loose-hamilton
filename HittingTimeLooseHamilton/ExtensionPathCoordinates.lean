module

public import HittingTimeLooseHamilton.OrderedPathCoordinates

public section

noncomputable section
namespace LooseHamilton
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V] {r M : ℕ} {ell : V → ℕ}

/-- The complement of a terminal prefix, in the complete-edge universe, is
exactly the existing missing-edge subtype. -/
@[expose] def outsideMissingEquiv (F : TerminalState V r M ell) :
    OutsideVertex (liftEdges r F.val) ≃ MissingEdge F where
  toFun x := ⟨x.val.val,mem_sdiff.mpr ⟨x.val.property,by
    intro hx; exact x.property ((mem_liftEdges _ _).mpr hx)⟩⟩
  invFun e := ⟨⟨e.val,(mem_sdiff.mp e.property).1⟩,by
    intro he; exact (mem_sdiff.mp e.property).2 ((mem_liftEdges _ _).mp he)⟩
  left_inv x := by cases x; rfl
  right_inv e := by cases e; rfl

lemma outsideMissing_card (F : TerminalState V r M ell) :
    Fintype.card (OutsideVertex (liftEdges r F.val)) = (completeEdges V r).card-M :=
  (Fintype.card_congr (outsideMissingEquiv F)).trans (missing_card F)

/-- Uniform permutations in the original extension model are equivalent to
all orders of the complement of its terminal prefix. -/
@[expose] def outsideRankEquiv (F : TerminalState V r M ell) :
    MissingOrder V r M ≃ FiniteOrder (OutsideVertex (liftEdges r F.val)) :=
  (missingOrderEquiv F).trans
    (Equiv.equivCongr (outsideMissingEquiv F).symm (finCongr (outsideMissing_card F).symm))

@[simp] lemma outsideRankEquiv_apply_val (F : TerminalState V r M ell)
    (σ : MissingOrder V r M) (e : OutsideVertex (liftEdges r F.val)) :
    ((outsideRankEquiv F σ) e).val = (missingOrder F σ (outsideMissingEquiv F e)).val := by
  rfl

/-- The entire suffix path in these coordinates is exactly the extensionState
path, including clamping below M and saturation above the complete graph. -/
theorem outsideExtensionPath_eq_extensionState (F : TerminalState V r M ell)
    (σ : MissingOrder V r M) (j : ℕ) :
    (outsideExtensionPath (liftEdges r F.val) (outsideRankEquiv F σ) j).image Subtype.val =
      extensionState F σ j := by
  rw [outsideExtensionPath, image_union, liftEdges_image F.property.1]
  unfold extensionState
  congr 1
  rw [image_image, liftEdges_card F.property.1, F.property.2.1]
  ext e
  simp only [mem_image,mem_orderPrefix,mem_filter,mem_univ,true_and,
    outsideRankEquiv_apply_val,Function.comp_apply]
  constructor
  · rintro ⟨x,hx,hxe⟩
    exact ⟨outsideMissingEquiv F x,hx,hxe⟩
  · rintro ⟨x,hx,hxe⟩
    refine ⟨(outsideMissingEquiv F).symm x,?_,?_⟩
    · simpa only [Equiv.apply_symm_apply] using hx
    · exact hxe

end LooseHamilton
