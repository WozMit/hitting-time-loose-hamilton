module

public import HittingTimeLooseHamilton.RootSamplingModels
public import HittingTimeLooseHamilton.RootLinkPrescribed
public import HittingTimeLooseHamilton.RootLinkScales
public import HittingTimeLooseHamilton.CoreConditionalCounting

public section

/-! Exact prescribed-inner strata and the remaining-universe density bound. -/
noncomputable section
namespace LooseHamilton
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

lemma rootFreeEdges_disjoint_root (r : ℕ) (y : V) (F : SimpleHypergraph V) :
    Disjoint (rootFreeEdges y F) (rootEdgeUniverse r y) := by
  apply disjoint_left.mpr
  intro e he hu
  exact (mem_filter.mp he).2 (mem_filter.mp hu).2

lemma conditional_event_congr_on {Ω : Type*} [Fintype Ω] (p : FiniteEntropy.Law Ω)
    (E P Q : Ω → Prop) (hE : 0 < p.event E) (heq : ∀ω,E ω → (P ω ↔ Q ω)) :
    (p.condition E hE).event P=(p.condition E hE).event Q := by
  rw [condition_event_eq_joint,condition_event_eq_joint]
  congr 2
  funext ω
  apply propext
  constructor
  · rintro ⟨he,hp⟩
    exact ⟨he,(heq ω he).mp hp⟩
  · rintro ⟨he,hq⟩
    exact ⟨he,(heq ω he).mpr hq⟩

omit [Fintype V] in
lemma root_complement_bad_count (H U B₀ R Γ : SimpleHypergraph V)
    (hH : H\U=B₀∪R) (hB : Disjoint B₀ Γ) :
    H∩Γ=((H∩U)∪R)∩Γ := by
  have hr := sdiff_union_inter H U
  rw [hH] at hr
  have hrec : H=(B₀∪R)∪(H∩U) := hr.symm
  rw [hrec]
  ext e
  simp only [mem_inter,mem_union]
  constructor
  · rintro ⟨(hB'|hR)|hU,hΓ⟩
    · exact False.elim (disjoint_left.mp hB hB' hΓ)
    · exact ⟨Or.inr hR,hΓ⟩
    · exact ⟨Or.inl ⟨Or.inr hU,hU.2⟩,hΓ⟩
  · rintro ⟨(⟨hH',hU⟩|hR),hΓ⟩
    · exact ⟨hH',hΓ⟩
    · exact ⟨Or.inl (Or.inr hR),hΓ⟩

lemma root_remaining_density (r : ℕ) (y : V) (Γ R : SimpleHypergraph V) (h : ℕ)
    (hR : R ⊆ rootEdgeUniverse r y) (hRh : R.card ≤ h)
    (hU : 0 < (rootEdgeUniverse r y).card) (hh : 2*h ≤ (rootEdgeUniverse r y).card) :
    0 < (rootEdgeUniverse r y\R).card ∧
      (((Γ∩(rootEdgeUniverse r y\R)).card:ℝ)/(rootEdgeUniverse r y\R).card) ≤
        2*rootLinkDensity r y Γ := by
  have hRc := card_le_card hR
  have hpos : 0 < (rootEdgeUniverse r y\R).card := by rw [card_sdiff_of_subset hR]; omega
  refine ⟨hpos,?_⟩
  have hUreal : (0:ℝ) < (rootEdgeUniverse r y).card := by exact_mod_cast hU
  have htwo : 2*(R.card:ℝ) ≤ (rootEdgeUniverse r y).card := by exact_mod_cast (show 2*R.card ≤ _ by omega)
  have hρ : 0 ≤ rootLinkDensity r y Γ := by unfold rootLinkDensity; positivity
  have hnum : ((Γ∩(rootEdgeUniverse r y\R)).card:ℝ) ≤
      rootLinkDensity r y Γ*(rootEdgeUniverse r y).card := by
    unfold rootLinkDensity
    rw [div_mul_cancel₀ _ hUreal.ne']
    exact_mod_cast card_le_card (inter_subset_left : Γ∩(rootEdgeUniverse r y\R) ⊆ Γ)
  have hb := rootLink_remaining_density hUreal htwo hρ hnum
  rw [card_sdiff_of_subset hR,Nat.cast_sub hRc]
  exact hb
end LooseHamilton
