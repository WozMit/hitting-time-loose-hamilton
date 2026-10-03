module

public import HittingTimeLooseHamilton.UniformOrderSupportTails
public import HittingTimeLooseHamilton.Models

public section

/-! Conditional support sampling in the extension, with the terminal graph fixed. -/
noncomputable section
namespace LooseHamilton
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {r M : ℕ} {ell : V → ℕ}
attribute [local instance] Classical.propDecidable

/-- Uniform missing-edge positions reindexed as an order of the missing-edge subtype. -/
@[expose] def extensionOrderEquiv (F : TerminalState V r M ell) :
    MissingOrder V r M ≃ FiniteOrder (MissingEdge F) :=
  (missingOrderEquiv F).trans (Equiv.equivCongr (Equiv.refl _)
    (finCongr (missing_card F).symm))

@[expose] def missingPrefix (F : TerminalState V r M ell) (σ : MissingOrder V r M) (m : ℕ) :
    Finset (MissingEdge F) := orderPrefix (extensionOrderEquiv F σ) m

@[simp] lemma mem_missingPrefix (F : TerminalState V r M ell) (σ : MissingOrder V r M)
    (m : ℕ) (e : MissingEdge F) :
    e ∈ missingPrefix F σ m ↔ (missingOrder F σ e).val < m := by
  simp [missingPrefix,mem_orderPrefix,extensionOrderEquiv,Equiv.equivCongr,missingOrderEquiv]

lemma extensionState_eq_prefix (F : TerminalState V r M ell)
    (σ : MissingOrder V r M) (j : ℕ) :
    extensionState F σ j = F.val ∪ (missingPrefix F σ (j-M)).image Subtype.val := by
  unfold extensionState
  congr 1

@[expose] def missingSupport (F : TerminalState V r M ell) (P : Finset V → Prop) :
    Finset (MissingEdge F) := univ.filter (fun e => P e.val)

lemma extension_filter_card (F : TerminalState V r M ell) (σ : MissingOrder V r M)
    (j : ℕ) (P : Finset V → Prop) [DecidablePred P] :
    ((extensionState F σ j).filter P).card =
      (F.val.filter P).card + (missingSupport F P ∩ missingPrefix F σ (j-M)).card := by
  rw [extensionState_eq_prefix,filter_union]
  have hd : Disjoint (F.val.filter P)
      (((missingPrefix F σ (j-M)).image Subtype.val).filter P) := by
    apply disjoint_left.mpr
    intro e he hnew
    obtain ⟨x,hx,rfl⟩ := mem_image.mp (mem_filter.mp hnew).1
    exact (mem_sdiff.mp x.property).2 (mem_filter.mp he).1
  rw [card_union_of_disjoint hd]
  congr 1
  have he : (((missingPrefix F σ (j-M)).image Subtype.val).filter P) =
      (missingSupport F P ∩ missingPrefix F σ (j-M)).image Subtype.val := by
    ext e
    simp only [mem_filter,mem_image,mem_inter,missingSupport,mem_univ,true_and]
    constructor
    · rintro ⟨⟨x,hx,rfl⟩,hp⟩; exact ⟨x,⟨hp,hx⟩,rfl⟩
    · rintro ⟨x,⟨hp,hx⟩,rfl⟩; exact ⟨⟨x,hx,rfl⟩,hp⟩
  rw [he,card_image_of_injective _ Subtype.val_injective]

lemma missing_support_upper_exp (F : TerminalState V r M ell) (m k : ℕ)
    (hm : m ≤ (completeEdges V r).card-M) (hN : M < (completeEdges V r).card)
    (D : Finset (MissingEdge F)) (t : ℝ) (ht : 0 < t) :
    (FiniteEntropy.uniform : FiniteEntropy.Law (MissingOrder V r M)).event
      (fun σ => k ≤ (D ∩ missingPrefix F σ m).card) ≤
      Real.exp (t*(D.card:ℝ)*m/((completeEdges V r).card-M:ℕ))/t^k := by
  have h := order_support_upper_exp m k
    (by simpa only [missing_card] using hm) (by simpa only [missing_card] using Nat.sub_pos_of_lt hN) D t ht
  have he := FiniteEntropy.Law.uniform_event_equiv (extensionOrderEquiv F)
    (fun σ => k ≤ (D ∩ orderPrefix σ m).card)
  change _ ≤ _
  rw [show (fun σ : MissingOrder V r M => k ≤ (D ∩ missingPrefix F σ m).card) =
      (fun σ => k ≤ (D ∩ orderPrefix (extensionOrderEquiv F σ) m).card) from rfl,he]
  simpa only [missing_card] using h

lemma missing_support_lower_exp (F : TerminalState V r M ell) (m k : ℕ)
    (hm : m ≤ (completeEdges V r).card-M) (hN : M < (completeEdges V r).card)
    (D : Finset (MissingEdge F)) (q : ℝ) (hq : 0 < q) (hq1 : q ≤ 1) :
    (FiniteEntropy.uniform : FiniteEntropy.Law (MissingOrder V r M)).event
      (fun σ => (missingPrefix F σ m ∩ D).card ≤ k) ≤
      Real.exp (-(m:ℝ)/((completeEdges V r).card-M:ℕ)*D.card*(1-q)-(k:ℝ)*Real.log q) := by
  have h := order_support_lower_exp m k
    (by simpa only [missing_card] using hm) (by simpa only [missing_card] using Nat.sub_pos_of_lt hN) D q hq hq1
  have he := FiniteEntropy.Law.uniform_event_equiv (extensionOrderEquiv F)
    (fun σ => (orderPrefix σ m ∩ D).card ≤ k)
  rw [show (fun σ : MissingOrder V r M => (missingPrefix F σ m ∩ D).card ≤ k) =
      (fun σ => (orderPrefix (extensionOrderEquiv F σ) m ∩ D).card ≤ k) from rfl,he]
  simpa only [missing_card] using h
end LooseHamilton
