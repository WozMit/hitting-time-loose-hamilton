module

public import HittingTimeLooseHamilton.RootLinkFeasibleTailTransfer
public import HittingTimeLooseHamilton.RootOuterHitCoupling

public section

noncomputable section
namespace LooseHamilton
open Finset
attribute [local instance] Classical.propDecidable
variable {A : Type*} [Fintype A] [DecidableEq A]

/-- The finite tail for the actual nested law conditioned on the inner link hitting one star. -/
theorem conditioned_nested_prescribed_root_tail (U Γ R S : Finset A) (b q Q h : ℕ) (ρ : ℝ)
    [Nonempty (FiniteNestedSubsets U b q)]
    (hS : S⊆U) (hbq : b≤q) (hqU : q≤U.card) (hU : 0<U.card)
    (hqQ : q≤Q) (hQ : 12*(h+1)≤Q) (hR : R.card≤h)
    (hρ : 0≤ρ) (hsmall : 8*ρ≤1)
    (hden : ((Γ∩U).card:ℝ)/U.card≤2*ρ)
    (hE : 0<(FiniteEntropy.uniform : FiniteEntropy.Law (FiniteNestedSubsets U b q)).event
      (fun p=>¬Disjoint p.val.1 S)) :
    ((FiniteEntropy.uniform : FiniteEntropy.Law (FiniteNestedSubsets U b q)).condition
      (fun p=>¬Disjoint p.val.1 S) hE).event
      (fun B=>2*Q≤3*((B.val.2∪R)∩Γ).card) ≤ (8*ρ)^((Q:ℝ)/4) := by
  letI : Nonempty ↥(U.powersetCard b) := Nonempty.map (nestedInner U b q) inferInstance
  letI : Nonempty ↥(U.powersetCard q) := Nonempty.map (nestedOuter U b q) inferInstance
  have he : (fun p : FiniteNestedSubsets U b q=>¬Disjoint p.val.1 S)=
      (fun p=>1≤(p.val.1∩S).card) := by
    funext p
    apply propext
    rw [disjoint_iff_inter_eq_empty,←card_eq_zero]
    omega
  have hpos : 0<(FiniteEntropy.uniform : FiniteEntropy.Law (FiniteNestedSubsets U b q)).event
      (fun p=>1≤(p.val.1∩S).card) := by rwa [←he]
  have hi : 0<(FiniteEntropy.uniform : FiniteEntropy.Law ↥(U.powersetCard b)).event
      (fun T=>1≤(T.val∩S).card) := by
    obtain ⟨w,hw⟩ := exists_of_event_pos
      (FiniteEntropy.uniform : FiniteEntropy.Law (FiniteNestedSubsets U b q)) _ hpos
    rw [FiniteEntropy.Law.uniform_event]
    apply div_pos
    · exact_mod_cast card_pos.mpr ⟨nestedInner U b q w,mem_filter.mpr ⟨mem_univ _,hw⟩⟩
    · exact_mod_cast Fintype.card_pos
  obtain ⟨π,hp,hy,hswap⟩ := root_outer_hit_coupling U S hS b q hbq hqU hi
  have ht := coupled_prescribed_root_tail_finset U Γ R q Q h ρ hqU hU _ π hp hy
    (fun z hz=>hswap z hz Γ) hqQ hQ hR hρ hsmall hden
  rw [FiniteEntropy.Law.event_map] at ht
  simp only [FiniteEntropy.Law.conditionOr,dif_pos hpos] at ht
  simpa only [he] using ht

/-- Uniformity plus the proved zero-or-single-star description yields the finite root-link tail.
There is no assumed probability or coupling estimate in this statement. -/
theorem uniform_feasible_zero_or_star_tail (U Γ R : Finset A) (b q Q h : ℕ) (ρ : ℝ)
    (P : FiniteNestedSubsets U b q → Prop)
    [Nonempty {p : FiniteNestedSubsets U b q // P p}]
    (hqU : q≤U.card) (hU : 0<U.card) (hqQ : q≤Q) (hQ : 12*(h+1)≤Q) (hR : R.card≤h)
    (hρ : 0≤ρ) (hsmall : 8*ρ≤1) (hden : ((Γ∩U).card:ℝ)/U.card≤2*ρ)
    (hconstraint : (∀p,P p) ∨ ∃S⊆U,∀p,P p↔¬Disjoint p.val.1 S) :
    (FiniteEntropy.uniform : FiniteEntropy.Law {p : FiniteNestedSubsets U b q // P p}).event
      (fun B=>2*Q≤3*((B.val.val.2∪R)∩Γ).card) ≤ (8*ρ)^((Q:ℝ)/4) := by
  obtain ⟨w⟩ := ‹Nonempty {p : FiniteNestedSubsets U b q // P p}›
  letI : Nonempty (FiniteNestedSubsets U b q) := ⟨w.val⟩
  have hbq : b≤q := by
    have hh := card_le_card w.val.property.1
    rw [w.val.property.2.1,(mem_powersetCard.mp w.val.property.2.2).2] at hh
    exact hh
  apply uniform_feasible_zero_or_star_event_bound U b q P
    (fun B=>2*Q≤3*((B.val.2∪R)∩Γ).card) _ hconstraint
  · exact uniform_nested_prescribed_root_tail U Γ R b q Q h ρ hqU hU hqQ hQ hR hρ hsmall hden
  · intro S hS hE
    exact conditioned_nested_prescribed_root_tail U Γ R S b q Q h ρ hS hbq hqU hU
      hqQ hQ hR hρ hsmall hden hE
end LooseHamilton
