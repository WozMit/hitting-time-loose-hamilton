module

public import HittingTimeLooseHamilton.SurvivalTiltedLaw

public section

/-! Finset-label interface to the survival-tilted variance transfer.
Nothing requires the objects' eventual support map to be injective. -/
noncomputable section
namespace LooseHamilton.SurvivalTilt
open Finset FiniteEntropy
open scoped BigOperators
variable {A : Type*}

/-- Indexed finite-family version; overlap is averaged over the original labels. -/
theorem normalized_variance_finset (F : Finset A) (hF : F.Nonempty)
    (q : A → ℝ) (hq : ∀ a ∈ F, 0 < q a) (P I : A → A → ℝ)
    (C z L : ℝ) (hC : 0 ≤ C) (hz : 0 < z) (hL : 0 ≤ L)
    (hlo : ∀ a ∈ F, z ≤ q a) (hhi : ∀ a ∈ F, q a ≤ L*z)
    (hI : ∀ a ∈ F, ∀ b ∈ F, 0 ≤ I a b)
    (hP : ∀ a ∈ F, ∀ b ∈ F, P a b/(q a*q b) ≤ 1+C*I a b) :
    ((∑ a ∈ F, ∑ b ∈ F, P a b) - (∑ a ∈ F, q a)^2)/(∑ a ∈ F, q a)^2 ≤
      L^2*C*((∑ a ∈ F, ∑ b ∈ F, I a b)/(F.card:ℝ)^2) := by
  classical
  letI : Nonempty ↥F := ⟨⟨hF.choose,hF.choose_spec⟩⟩
  have h := normalized_variance_le (fun a : ↥F => q a.val) (fun a => hq a.val a.property)
    (fun a b : ↥F => P a.val b.val) (fun a b : ↥F => I a.val b.val)
    C z L hC hz hL (fun a => hlo a.val a.property) (fun a => hhi a.val a.property)
    (fun a b => hI a.val a.property b.val b.property)
    (fun a b => hP a.val a.property b.val b.property)
  rw [uniform_pairMean] at h
  have hs (g : A → A → ℝ) : (∑ a : ↥F, ∑ b : ↥F, g a.val b.val) =
      ∑ a ∈ F, ∑ b ∈ F, g a b := by
    rw [sum_coe_sort F (fun a => ∑ b : ↥F, g a b.val)]
    apply sum_congr rfl
    intro a _
    exact sum_coe_sort F (fun b => g a b)
  rw [hs P, hs I, sum_coe_sort F q, Fintype.card_coe] at h
  exact h

end LooseHamilton.SurvivalTilt
