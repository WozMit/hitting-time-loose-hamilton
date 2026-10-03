module

public import HittingTimeLooseHamilton.OrderComplementRefinement

public section

/-! Uniform missing-subset kernel given an exact prefix of a random order. -/
noncomputable section
namespace LooseHamilton
open Finset
attribute [local instance] Classical.propDecidable
variable {A : Type*} [Fintype A] [DecidableEq A]

theorem ordered_extension_kernel (K : Finset A) (j : ℕ)
    (hKj : K.card ≤ j) (hj : j ≤ Fintype.card A) (P : Finset A → Prop) :
    ((univ.filter (fun σ : FiniteOrder A => orderPrefix σ K.card = K ∧
      P (orderPrefix σ j))).card : ℝ) / Fintype.card (FiniteOrder A) =
    ((univ.filter (fun σ : FiniteOrder A => orderPrefix σ K.card = K)).card : ℝ) /
      Fintype.card (FiniteOrder A) *
      ((((univ \ K).powersetCard (j-K.card)).filter (fun S => P (K ∪ S))).card : ℝ) /
        ((univ \ K).powersetCard (j-K.card)).card := by
  classical
  let E : FiniteOrder A → Prop := fun σ => K ⊆ orderPrefix σ K.card ∧
    (earlyOutside σ K j).card = j-K.card
  let U := (univ \ K).powersetCard (j-K.card)
  have he (σ : FiniteOrder A) : E σ ↔ orderPrefix σ K.card = K := by
    constructor
    · intro h
      exact (eq_of_subset_of_card_le h.1 (by rw [orderPrefix_card _ _ (hKj.trans hj)])).symm
    · intro h
      have hs : K ⊆ orderPrefix σ j := by
        rw [← h]
        intro a ha
        exact (mem_orderPrefix _ _ _).mpr (lt_of_lt_of_le ((mem_orderPrefix _ _ _).mp ha) hKj)
      refine ⟨by rw [h],?_⟩
      rw [earlyOutside,card_sdiff_of_subset hs,orderPrefix_card _ _ hj]
  have hu : U.Nonempty := by
    apply powersetCard_nonempty.mpr
    simp only [card_sdiff_of_subset (subset_univ K),card_univ]
    omega
  have hmap (σ : FiniteOrder A) (h : E σ) : earlyOutside σ K j ∈ U :=
    mem_powersetCard.mpr ⟨sdiff_subset_sdiff (subset_univ _) (Subset.refl _),h.2⟩
  have hequal : ∀ S ∈ U, ∀ T ∈ U,
      (univ.filter (fun σ => E σ ∧ earlyOutside σ K j = S)).card =
      (univ.filter (fun σ => E σ ∧ earlyOutside σ K j = T)).card := by
    intro S hS T hT
    obtain ⟨hS,hSc⟩ := mem_powersetCard.mp hS
    obtain ⟨hT,hTc⟩ := mem_powersetCard.mp hT
    exact earlyOutside_fibres_equal K S T j K.card (j-K.card) hS hT hSc hTc
  have h := Kahn.Ordering.uniform_refinement_probability E
    (fun σ => earlyOutside σ K j) U hu hmap hequal (fun S => P (K ∪ S))
  have hid (σ : FiniteOrder A) (hσ : orderPrefix σ K.card = K) :
      K ∪ earlyOutside σ K j = orderPrefix σ j := by
    apply union_sdiff_of_subset
    rw [← hσ]
    intro a ha
    exact (mem_orderPrefix _ _ _).mpr (lt_of_lt_of_le ((mem_orderPrefix _ _ _).mp ha) hKj)
  have hev : (fun σ => E σ ∧ P (K ∪ earlyOutside σ K j)) =
      (fun σ => orderPrefix σ K.card = K ∧ P (orderPrefix σ j)) := by
    funext σ
    apply propext
    rw [he]
    constructor
    · rintro ⟨hσ,hp⟩; exact ⟨hσ,by simpa only [hid σ hσ] using hp⟩
    · rintro ⟨hσ,hp⟩; exact ⟨hσ,by simpa only [hid σ hσ] using hp⟩
  simp_rw [hev] at h
  have hfilter : univ.filter E = univ.filter (fun σ => orderPrefix σ K.card = K) := by
    ext σ; simp only [mem_filter,mem_univ,true_and,he]
  rw [hfilter] at h
  exact h
end LooseHamilton
