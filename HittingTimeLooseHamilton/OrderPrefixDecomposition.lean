module

public import HittingTimeLooseHamilton.UniformPrefixProbability
public import Mathlib.Logic.Equiv.Sum

public section
noncomputable section
namespace LooseHamilton
open Finset
attribute [local instance] Classical.propDecidable
variable {A : Type*} [Fintype A] [DecidableEq A]

abbrev PrefixOrderFiber (K : Finset A) := {σ : FiniteOrder A // orderPrefix σ K.card = K}
abbrev OutsideVertex (K : Finset A) := {x : A // x ∉ K}

lemma order_split_card (K : Finset A) : K.card + Fintype.card (OutsideVertex K) = Fintype.card A := by
  rw [Fintype.card_subtype_compl,Fintype.card_coe]
  exact Nat.add_sub_of_le (card_le_univ K)

/-- Concatenate independent internal and external orders. -/
@[expose] def concatenateOrder (K : Finset A) (ρ : FiniteOrder ↥K)
    (τ : FiniteOrder (OutsideVertex K)) : FiniteOrder A :=
  (Equiv.sumCompl (fun a => a ∈ K)).symm.trans
    ((Equiv.sumCongr ρ τ).trans (finSumFinEquiv.trans
      (finCongr (by simpa only [Fintype.card_coe] using order_split_card K))))

lemma concatenateOrder_inside (K : Finset A) (ρ : FiniteOrder ↥K)
    (τ : FiniteOrder (OutsideVertex K)) (x : ↥K) :
    ((concatenateOrder K ρ τ) x.val).val = (ρ x).val := by
  simp [concatenateOrder,Equiv.sumCompl_symm_apply_of_pos x.property]

lemma concatenateOrder_outside (K : Finset A) (ρ : FiniteOrder ↥K)
    (τ : FiniteOrder (OutsideVertex K)) (x : OutsideVertex K) :
    ((concatenateOrder K ρ τ) x.val).val = K.card + (τ x).val := by
  simp [concatenateOrder,Equiv.sumCompl_symm_apply_of_neg x.property]

lemma concatenateOrder_prefix (K : Finset A) (ρ : FiniteOrder ↥K)
    (τ : FiniteOrder (OutsideVertex K)) : orderPrefix (concatenateOrder K ρ τ) K.card = K := by
  ext x
  rw [mem_orderPrefix]
  by_cases hx : x ∈ K
  · rw [concatenateOrder_inside K ρ τ ⟨x,hx⟩]
    have ht := (ρ ⟨x,hx⟩).isLt
    simpa only [Fintype.card_coe,iff_true,hx] using ht
  · rw [concatenateOrder_outside K ρ τ ⟨x,hx⟩]
    simp [hx]

lemma prefixFiber_mem_iff (K : Finset A) (σ : PrefixOrderFiber K) (x : A) :
    x ∈ K ↔ (σ.val x).val < K.card := by
  have hh := congrArg (fun S : Finset A => x ∈ S) σ.property
  exact (Iff.of_eq hh).symm.trans (mem_orderPrefix σ.val K.card x)

@[expose] def prefixInternalOrder (K : Finset A) (σ : PrefixOrderFiber K) : FiniteOrder ↥K where
  toFun x := ⟨(σ.val x.val).val,by simpa only [Fintype.card_coe] using
    (prefixFiber_mem_iff K σ x.val).mp x.property⟩
  invFun i := ⟨σ.val.symm ⟨i.val,by
    have hi : i.val < K.card := by simpa only [Fintype.card_coe] using i.isLt
    exact hi.trans_le (card_le_univ K)⟩,
    (prefixFiber_mem_iff K σ _).mpr (by simp only [Equiv.apply_symm_apply]; simpa only [Fintype.card_coe] using i.isLt)⟩
  left_inv x := by apply Subtype.ext; simp
  right_inv i := by apply Fin.ext; simp

@[expose] def prefixOutsideOrder (K : Finset A) (σ : PrefixOrderFiber K) : FiniteOrder (OutsideVertex K) where
  toFun x := ⟨(σ.val x.val).val-K.card,by
    have hm : K.card ≤ (σ.val x.val).val := Nat.le_of_not_gt
      (fun hh => x.property ((prefixFiber_mem_iff K σ x.val).mpr hh))
    have hi := (σ.val x.val).isLt
    have hc := order_split_card K
    omega⟩
  invFun i := ⟨σ.val.symm ⟨K.card+i.val,by have hi := i.isLt; have hc := order_split_card K; omega⟩,
    by intro hx
       have hh := (prefixFiber_mem_iff K σ _).mp hx
       simp only [Equiv.apply_symm_apply] at hh
       omega⟩
  left_inv x := by
    apply Subtype.ext
    apply σ.val.injective
    simp only [Equiv.apply_symm_apply]
    apply Fin.ext
    have hm : K.card ≤ (σ.val x.val).val := Nat.le_of_not_gt
      (fun hh => x.property ((prefixFiber_mem_iff K σ x.val).mpr hh))
    simp only
    omega
  right_inv i := by apply Fin.ext; simp

/-- Exact decomposition of every full order with a specified initial set. -/
@[expose] def prefixOrderEquiv (K : Finset A) :
    PrefixOrderFiber K ≃ FiniteOrder ↥K × FiniteOrder (OutsideVertex K) where
  toFun σ := (prefixInternalOrder K σ,prefixOutsideOrder K σ)
  invFun p := ⟨concatenateOrder K p.1 p.2,concatenateOrder_prefix K p.1 p.2⟩
  left_inv σ := by
    apply Subtype.ext
    apply Equiv.ext
    intro x
    apply Fin.ext
    by_cases hx : x ∈ K
    · rw [concatenateOrder_inside K _ _ ⟨x,hx⟩]; rfl
    · rw [concatenateOrder_outside K _ _ ⟨x,hx⟩]
      change K.card+((σ.val x).val-K.card) = (σ.val x).val
      have hh : ¬(σ.val x).val<K.card := fun hh => hx ((prefixFiber_mem_iff K σ x).mpr hh)
      omega
  right_inv p := by
    apply Prod.ext
    · apply Equiv.ext; intro x; apply Fin.ext
      exact concatenateOrder_inside K p.1 p.2 x
    · apply Equiv.ext; intro x; apply Fin.ext
      change ((concatenateOrder K p.1 p.2) x.val).val-K.card = (p.2 x).val
      rw [concatenateOrder_outside]; omega
end LooseHamilton
