module

public import HittingTimeLooseHamilton.ComplementSubsetSymmetry
public import HittingTimeLooseHamilton.KahnConditionalOrder

public section

/-! Exact conditional symmetry of the labels outside a prescribed edge set. -/
noncomputable section
namespace LooseHamilton
open Finset
variable {A : Type*} [Fintype A] [DecidableEq A]

/-- The early labels outside the prescribed later set. -/
@[expose] def earlyOutside (σ : FiniteOrder A) (K : Finset A) (a : ℕ) : Finset A :=
  orderPrefix σ a \ K

/-- Fixing the prescribed labels individually preserves their later inclusion
and gives equally sized fibres for every early complement subset. -/
theorem earlyOutside_fibres_equal (K S T : Finset A) (a b s : ℕ)
    (hS : S ⊆ univ \ K) (hT : T ⊆ univ \ K) (hSc : S.card = s) (hTc : T.card = s) :
    (univ.filter (fun σ : FiniteOrder A =>
      (K ⊆ orderPrefix σ b ∧ (earlyOutside σ K a).card = s) ∧ earlyOutside σ K a = S)).card =
    (univ.filter (fun σ : FiniteOrder A =>
      (K ⊆ orderPrefix σ b ∧ (earlyOutside σ K a).card = s) ∧ earlyOutside σ K a = T)).card := by
  classical
  obtain ⟨g,hfix,hmem⟩ := exists_perm_fix_set_maps_subsets K S T
    (subset_sdiff.mp hS).2 (subset_sdiff.mp hT).2 (hSc.trans hTc.symm)
  let e : FiniteOrder A ≃ FiniteOrder A := Equiv.equivCongr g (Equiv.refl _)
  have hgK (x : A) : g x ∈ K ↔ x ∈ K := by
    constructor
    · intro hx
      have hh : g x = x := g.injective (hfix (g x) hx)
      simpa only [hh] using hx
    · intro hx; simpa only [hfix x hx] using hx
  have hsymK (x : A) : g.symm x ∈ K ↔ x ∈ K := by
    simpa only [Equiv.apply_symm_apply] using (hgK (g.symm x)).symm
  apply Kahn.Ordering.card_event_eq_of_equiv _ _ e
  intro σ
  have houtside (x : A) : x ∈ earlyOutside (e σ) K a ↔ g.symm x ∈ earlyOutside σ K a := by
    simp only [earlyOutside,mem_sdiff,mem_orderPrefix]
    change ((σ (g.symm x)).val < a ∧ x ∉ K) ↔ ((σ (g.symm x)).val < a ∧ g.symm x ∉ K)
    rw [hsymK]
  have hE : K ⊆ orderPrefix σ b ↔ K ⊆ orderPrefix (e σ) b := by
    have hpoint (x : A) (hx : x ∈ K) : (e σ) x = σ x := by
      change σ (g.symm x) = σ x
      rw [g.symm_apply_eq.mpr (hfix x hx).symm]
    constructor <;> intro h x hx
    · rw [mem_orderPrefix,hpoint x hx]
      exact (mem_orderPrefix _ _ _).mp (h hx)
    · have hh := (mem_orderPrefix _ _ _).mp (h hx)
      rw [hpoint x hx] at hh
      exact (mem_orderPrefix _ _ _).mpr hh
  have hcard : (earlyOutside (e σ) K a).card = (earlyOutside σ K a).card := by
    apply card_equiv g.symm
    exact houtside
  have hset : earlyOutside σ K a = S ↔ earlyOutside (e σ) K a = T := by
    constructor
    · intro hs
      ext x
      rw [houtside,hs,hmem]
      simp
    · intro hs
      ext x
      have hh := houtside (g x)
      rw [hs,Equiv.symm_apply_apply] at hh
      exact hh.symm.trans (hmem x).symm
  rw [hcard]
  exact and_congr (and_congr hE Iff.rfl) hset

/-- Exact conditional avoidance, keeping the actual probability of the
conditioning event as a factor. This includes conditioning events of mass zero. -/
theorem uniform_earlyOutside_avoidance (K D : Finset A) (a b s : ℕ)
    (hs : s ≤ (univ \ K).card) (hD : D ⊆ univ \ K) :
    ((univ.filter (fun σ : FiniteOrder A =>
      (K ⊆ orderPrefix σ b ∧ (earlyOutside σ K a).card = s) ∧
        Disjoint (earlyOutside σ K a) D)).card : ℝ) / Fintype.card (FiniteOrder A) =
    ((univ.filter (fun σ : FiniteOrder A =>
      K ⊆ orderPrefix σ b ∧ (earlyOutside σ K a).card = s)).card : ℝ) /
        Fintype.card (FiniteOrder A) *
      (((univ \ K).card - D.card).choose s : ℝ) / ((univ \ K).card.choose s : ℝ) := by
  classical
  let E : FiniteOrder A → Prop := fun σ => K ⊆ orderPrefix σ b ∧ (earlyOutside σ K a).card = s
  let U := (univ \ K).powersetCard s
  have hmap : ∀ σ, E σ → earlyOutside σ K a ∈ U := by
    intro σ hσ
    exact mem_powersetCard.mpr ⟨sdiff_subset_sdiff (subset_univ _) (Subset.refl K),hσ.2⟩
  have hequal : ∀ S ∈ U, ∀ T ∈ U,
      (univ.filter (fun σ => E σ ∧ earlyOutside σ K a = S)).card =
        (univ.filter (fun σ => E σ ∧ earlyOutside σ K a = T)).card := by
    intro S hS T hT
    obtain ⟨hS,hSc⟩ := mem_powersetCard.mp hS
    obtain ⟨hT,hTc⟩ := mem_powersetCard.mp hT
    exact earlyOutside_fibres_equal K S T a b s hS hT hSc hTc
  have hh := Kahn.Ordering.uniform_refinement_probability E (fun σ => earlyOutside σ K a)
    U (powersetCard_nonempty.mpr hs) hmap hequal (fun F => Disjoint F D)
  have hfilter : U.filter (fun F => Disjoint F D) = ((univ \ K) \ D).powersetCard s := by
    ext F
    simp only [U,mem_filter,mem_powersetCard,subset_sdiff]
    tauto
  rw [hfilter,card_powersetCard,card_sdiff_of_subset hD,show U.card = (univ \ K).card.choose s from card_powersetCard _ _] at hh
  exact hh
end LooseHamilton
