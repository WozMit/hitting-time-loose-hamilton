module

public import HittingTimeLooseHamilton.MissingOrderCoordinates

public section

/-! Exact last-added edge probability for a fixed terminal graph. -/
noncomputable section
namespace LooseHamilton
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V] {r M : ℕ} {ell : V → ℕ}

lemma extension_boundary_rank_iff (F : TerminalState V r M ell)
    (σ : MissingOrder V r M) (j : ℕ) (hMj : M<j)
    (H : SimpleHypergraph V) (hH : H ⊆ completeEdges V r)
    (e : MissingEdge F) (he : e.val ∈ H) (hF : F.val ⊆ H.erase e.val) :
    (extensionState F σ j=H ∧ extensionState F σ (j-1)=H.erase e.val) ↔
      orderPrefix (missingFiniteOrderEquiv F σ) (j-M)=liftMissing F H ∧
        (missingFiniteOrderEquiv F σ e).val=j-M-1 := by
  have hFH : F.val ⊆ H := hF.trans (erase_subset _ _)
  rw [←extensionState_eq_iff_missing_prefix F σ j H hH hFH,missingFiniteOrder_rank]
  constructor
  · rintro ⟨hj,hprev⟩
    refine ⟨hj,?_⟩
    have hnow : (missingOrder F σ e).val < j-M :=
      (mem_extensionState_missing F σ j e).mp (by rw [hj]; exact he)
    have hnot : ¬(missingOrder F σ e).val < j-1-M := by
      intro h
      have hh := (mem_extensionState_missing F σ (j-1) e).mpr h
      rw [hprev] at hh
      exact notMem_erase _ _ hh
    omega
  · rintro ⟨hj,hrank⟩
    refine ⟨hj,?_⟩
    ext f
    constructor
    · intro hf
      have hfH : f∈H := by rw [←hj]; exact extensionState_mono F σ (by omega : j-1 ≤ j) hf
      have hne : f≠e.val := by
        intro heq
        subst f
        have hh := (mem_extensionState_missing F σ (j-1) e).mp hf
        omega
      exact mem_erase.mpr ⟨hne,hfH⟩
    · intro hf
      obtain ⟨hne,hfH⟩ := mem_erase.mp hf
      by_cases hfF : f∈F.val
      · exact mem_union_left _ hfF
      · let a : MissingEdge F := ⟨f,mem_sdiff.mpr ⟨hH hfH,hfF⟩⟩
        have hrankA : (missingOrder F σ a).val < j-M :=
          (mem_extensionState_missing F σ j a).mp (by rw [hj]; exact hfH)
        have hneRank : (missingOrder F σ a).val ≠ (missingOrder F σ e).val := by
          intro hh
          have heq := (missingOrder F σ).injective (Fin.ext hh)
          exact hne (congrArg Subtype.val heq)
        exact (mem_extensionState_missing F σ (j-1) a).mpr (by omega)

lemma extension_fixed_boundary_probability (F : TerminalState V r M ell)
    (j : ℕ) (hMj : M<j) (hj : j ≤ (completeEdges V r).card)
    (H : SimpleHypergraph V) (hH : H ⊆ completeEdges V r) (hHj : H.card=j)
    (e : Finset V) (he : e∈H) (hF : F.val ⊆ H.erase e) :
    (FiniteEntropy.uniform : FiniteEntropy.Law (MissingOrder V r M)).event
      (fun σ => extensionState F σ j=H ∧ extensionState F σ (j-1)=H.erase e) =
        1/(((j-M:ℕ):ℝ)*(((completeEdges V r).card-M).choose (j-M):ℝ)) := by
  have heF : e∉F.val := by intro hh; exact notMem_erase e H (hF hh)
  let a : MissingEdge F := ⟨e,mem_sdiff.mpr ⟨hH he,heF⟩⟩
  have hFH : F.val ⊆ H := hF.trans (erase_subset _ _)
  have hm : j-M ≤ Fintype.card (MissingEdge F) := by rw [missing_card F]; omega
  have hc := uniform_order_boundary_probability (j-M) hm (by omega)
    (liftMissing F H) (by rw [liftMissing_card F H hH hFH,hHj]) a
    ((mem_liftMissing F H a).mpr he)
  have hequiv := FiniteEntropy.Law.uniform_event_equiv (missingFiniteOrderEquiv F)
    (fun σ => orderPrefix σ (j-M)=liftMissing F H ∧ (σ a).val=j-M-1)
  have hpred : (fun σ : MissingOrder V r M => extensionState F σ j=H ∧
      extensionState F σ (j-1)=H.erase e) =
      (fun σ => orderPrefix (missingFiniteOrderEquiv F σ) (j-M)=liftMissing F H ∧
        (missingFiniteOrderEquiv F σ a).val=j-M-1) := by
    funext σ
    exact propext (extension_boundary_rank_iff F σ j hMj H hH a he hF)
  rw [hpred,hequiv,FiniteEntropy.Law.uniform_event]
  simpa only [missing_card F] using hc

lemma extension_boundary_kernel (F : TerminalState V r M ell)
    (j : ℕ) (hMj : M<j) (hj : j ≤ (completeEdges V r).card)
    (H : SimpleHypergraph V) (hH : H ⊆ completeEdges V r) (hHj : H.card=j)
    (e : Finset V) (he : e∈H) :
    (FiniteEntropy.uniform : FiniteEntropy.Law (MissingOrder V r M)).event
      (fun σ => extensionState F σ j=H ∧ extensionState F σ (j-1)=H.erase e) =
        if F.val ⊆ H.erase e then
          1/(((j-M:ℕ):ℝ)*(((completeEdges V r).card-M).choose (j-M):ℝ)) else 0 := by
  classical
  split_ifs with hF
  · exact extension_fixed_boundary_probability F j hMj hj H hH hHj e he hF
  · have hfalse (σ : MissingOrder V r M) : ¬(extensionState F σ j=H ∧ extensionState F σ (j-1)=H.erase e) := by
      rintro ⟨_,hp⟩
      apply hF
      intro f hf
      rw [←hp]
      exact mem_union_left _ hf
    simp [FiniteEntropy.Law.event,hfalse]
end LooseHamilton
