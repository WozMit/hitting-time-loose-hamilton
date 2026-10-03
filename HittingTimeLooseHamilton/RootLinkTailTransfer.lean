module

public import HittingTimeLooseHamilton.KahnConditioning
public import Mathlib.Tactic

public section

/-! Tail comparison under a bounded-change coupling, including fixed prescribed elements. -/
noncomputable section
namespace LooseHamilton
open Finset

/-- Event monotonicity needs the implication only on positive-mass outcomes. -/
lemma event_le_of_positive_mass_imp {Ω : Type*} [Fintype Ω]
    (p : FiniteEntropy.Law Ω) (E F : Ω → Prop)
    (h : ∀ ω, 0 < p.mass ω → E ω → F ω) : p.event E ≤ p.event F := by
  classical
  apply sum_le_sum
  intro ω _
  by_cases he : E ω
  · by_cases hf : F ω
    · simp only [he,hf,if_true]; exact le_rfl
    · have hz : p.mass ω=0 := le_antisymm (le_of_not_gt (fun hp => hf (h ω hp he))) (p.nonneg ω)
      simp [he,hf,hz]
  · simp only [he,if_false]
    exact ite_nonneg (p.nonneg ω) (le_refl 0)

/-- A coupling that increases a natural statistic by at most t transfers every
upper tail with the exact threshold shift t. -/
theorem coupled_nat_tail_le {Ω Λ : Type*} [Fintype Ω] [Fintype Λ]
    (p : FiniteEntropy.Law Ω) (q : FiniteEntropy.Law Λ)
    (π : FiniteEntropy.Law (Ω × Λ)) (hp : π.map Prod.fst=p) (hq : π.map Prod.snd=q)
    (X : Ω → ℕ) (Y : Λ → ℕ) (t k : ℕ)
    (h : ∀ z, 0 < π.mass z → Y z.2 ≤ X z.1+t) :
    q.event (fun y => k ≤ Y y) ≤ p.event (fun x => k-t ≤ X x) := by
  rw [← hp,← hq,FiniteEntropy.Law.event_map,FiniteEntropy.Law.event_map]
  apply event_le_of_positive_mass_imp
  intro z hz hy
  have hh := h z hz
  omega

lemma prescribed_inter_card_le {A : Type*} [DecidableEq A]
    (T R Γ : Finset A) : ((T ∪ R) ∩ Γ).card ≤ (T ∩ Γ).card+R.card := by
  rw [union_inter_distrib_right]
  exact (card_union_le _ _).trans (Nat.add_le_add_left (card_le_card inter_subset_left) _)

/-- A one-swap coupling and at most h prescribed elements together cost at most
h+1 in the occupancy threshold. Prescribed elements need not lie in Gamma. -/
theorem coupled_prescribed_subset_tail {Ω Λ A : Type*}
    [Fintype Ω] [Fintype Λ] [DecidableEq A]
    (p : FiniteEntropy.Law Ω) (q : FiniteEntropy.Law Λ)
    (π : FiniteEntropy.Law (Ω × Λ)) (hp : π.map Prod.fst=p) (hq : π.map Prod.snd=q)
    (X : Ω → Finset A) (Y : Λ → Finset A) (Γ R : Finset A) (h k : ℕ)
    (hR : R.card ≤ h)
    (hc : ∀ z, 0 < π.mass z → (Y z.2 ∩ Γ).card ≤ (X z.1 ∩ Γ).card+1) :
    q.event (fun y => k ≤ ((Y y ∪ R) ∩ Γ).card) ≤
      p.event (fun x => k-(h+1) ≤ (X x ∩ Γ).card) := by
  apply coupled_nat_tail_le p q π hp hq (fun x => (X x ∩ Γ).card)
    (fun y => ((Y y ∪ R) ∩ Γ).card) (h+1) k
  intro z hz
  have h₁ := prescribed_inter_card_le (Y z.2) R Γ
  have h₂ := hc z hz
  omega

/-- Removing at most h prescribed points inflates density by at most N/(N-h). -/
theorem remaining_density_le {A : Type*} [DecidableEq A]
    (U Γ R : Finset A) (h : ℕ) (ρ : ℝ)
    (hρ : 0 ≤ ρ) (hR : R ⊆ U) (hh : R.card ≤ h) (hsmall : h < U.card)
    (hΓ : (Γ.card:ℝ) ≤ ρ*U.card) :
    (((Γ\R).card:ℝ)/(U\R).card) ≤ ρ*U.card/(U.card-h:ℕ) := by
  have hden : (0:ℝ)<(U.card-h:ℕ) := by exact_mod_cast Nat.sub_pos_of_lt hsmall
  have hdenle : ((U.card-h:ℕ):ℝ) ≤ (U\R).card := by
    rw [card_sdiff_of_subset hR]
    exact_mod_cast Nat.sub_le_sub_left hh U.card
  have hnum : ((Γ\R).card:ℝ) ≤ ρ*U.card :=
    (Nat.cast_le.mpr (card_le_card sdiff_subset)).trans hΓ
  exact div_le_div₀ (by positivity) hnum hden hdenle
end LooseHamilton
