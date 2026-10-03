module

public import HittingTimeLooseHamilton.RootLinkDeficit

public section

/-! Exact exposure of the inner status of prescribed current root edges. -/
noncomputable section
namespace LooseHamilton
open Finset
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]

omit [Fintype V] in
lemma sdiff_sdiff_eq_union_inter (F U R : SimpleHypergraph V) :
    F\(U\R)=(F\U)∪(F∩R) := by
  ext e
  simp only [mem_sdiff,mem_union,mem_inter]
  tauto

omit [Fintype V] in
lemma prescribed_root_partition (H U R : SimpleHypergraph V) (hRU : R ⊆ U) (hRH : R ⊆ H) :
    H∩U=(H∩(U\R))∪R := by
  ext e
  simp only [mem_inter,mem_sdiff,mem_union]
  constructor
  · rintro ⟨he,hu⟩
    by_cases hr : e∈R
    · exact Or.inr hr
    · exact Or.inl ⟨he,hu,hr⟩
  · rintro (⟨he,hu,_⟩|hr)
    · exact ⟨he,hu⟩
    · exact ⟨hRH hr,hRU hr⟩

omit [Fintype V] in
lemma sdiff_prescribed_parts_iff (F U R A I : SimpleHypergraph V)
    (hRU : R ⊆ U) (hAU : Disjoint A U) (hIR : I ⊆ R) :
    F\(U\R)=A∪I ↔ F\U=A ∧ F∩R=I := by
  constructor
  · intro h
    have hmem (e : Finset V) : (e∈F ∧ ¬(e∈U ∧ e∉R)) ↔ e∈A ∨ e∈I := by
      have hh := congrArg (fun S : SimpleHypergraph V => e∈S) h
      simpa only [mem_sdiff,mem_union] using Iff.of_eq hh
    constructor
    · ext e
      simp only [mem_sdiff]
      constructor
      · rintro ⟨he,hn⟩
        have hh := (hmem e).mp ⟨he,fun h=>hn h.1⟩
        exact hh.resolve_right (fun hi=>hn (hRU (hIR hi)))
      · intro he
        have hh := (hmem e).mpr (Or.inl he)
        exact ⟨hh.1,fun hu=>disjoint_left.mp hAU he hu⟩
    · ext e
      simp only [mem_inter]
      constructor
      · rintro ⟨he,hr⟩
        have hh := (hmem e).mp ⟨he,fun h=>h.2 hr⟩
        exact hh.resolve_left (fun ha=>disjoint_left.mp hAU ha (hRU hr))
      · intro hi
        have hh := (hmem e).mpr (Or.inr hi)
        exact ⟨hh.1,hIR hi⟩
  · rintro ⟨hA,hI⟩
    rw [sdiff_sdiff_eq_union_inter,hA,hI]

/-- Fixing root-free data and the prescribed-inner status is exactly a fixed-complement observation. -/
theorem root_link_prescribed_observation_iff (r : ℕ) (y : V)
    (F H A₀ B₀ R I : SimpleHypergraph V)
    (hF : F ⊆ completeEdges V r) (hH : H ⊆ completeEdges V r)
    (hR : R ⊆ rootEdgeUniverse r y)
    (hA : Disjoint A₀ (rootEdgeUniverse r y)) (hB : Disjoint B₀ (rootEdgeUniverse r y))
    (hI : I ⊆ R) :
    RootLinkObservation (rootEdgeUniverse r y\R) (A₀∪I) (B₀∪R) F H ↔
      rootFreeEdges y F=A₀ ∧ rootFreeEdges y H=B₀ ∧ R ⊆ H ∧ F∩R=I := by
  rw [RootLinkObservation,sdiff_prescribed_parts_iff F _ R A₀ I hR hA hI,
    sdiff_prescribed_parts_iff H _ R B₀ R hR hB (Subset.refl _),
    ←rootFreeEdges_eq_sdiff_universe r y F hF,←rootFreeEdges_eq_sdiff_universe r y H hH]
  have hr : H∩R=R ↔ R ⊆ H := by
    constructor
    · intro h
      rw [←h]
      exact inter_subset_left
    · intro h
      exact inter_eq_right.mpr h
  rw [hr]
  tauto

lemma rootAdjustedDeficit_mono (y : V) (ell : V → ℕ) {A A' : SimpleHypergraph V}
    (hA : A ⊆ A') (v : V) : rootAdjustedDeficit y ell A' v ≤ rootAdjustedDeficit y ell A v := by
  by_cases hv : v=y
  · simp [rootAdjustedDeficit,hv]
  · simp only [rootAdjustedDeficit,hv,if_false]
    have hd : vertexDegree A v ≤ vertexDegree A' v := by
      apply card_le_card
      exact filter_subset_filter _ hA
    omega

lemma rootAdjustedDeficit_sum_mono (y : V) (ell : V → ℕ) {A A' : SimpleHypergraph V}
    (hA : A ⊆ A') :
    (∑ v,rootAdjustedDeficit y ell A' v) ≤ ∑ v,rootAdjustedDeficit y ell A v :=
  sum_le_sum (fun v _=>rootAdjustedDeficit_mono y ell hA v)
end LooseHamilton
