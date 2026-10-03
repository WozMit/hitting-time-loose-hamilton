module

public import HittingTimeLooseHamilton.KahnLaw

public section

/-! A finite union with a unique witness is a disjoint union of events. -/
noncomputable section
namespace LooseHamilton
open Finset
open scoped BigOperators

/-- Finite additivity for events whose index is determined by the outcome. -/
theorem event_exists_eq_sum {Ω A : Type*} [Fintype Ω] [Fintype A]
    (p : FiniteEntropy.Law Ω) (E : A → Ω → Prop)
    (hunique : ∀ ω a b, E a ω → E b ω → a = b) :
    p.event (fun ω => ∃ a, E a ω) = ∑ a, p.event (E a) := by
  classical
  unfold FiniteEntropy.Law.event
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ω _
  by_cases h : ∃ a, E a ω
  · obtain ⟨a, ha⟩ := h
    rw [if_pos ⟨a,ha⟩]
    symm
    calc
      (∑ x, if E x ω then p.mass ω else 0) =
          (if E a ω then p.mass ω else 0) := by
        apply Finset.sum_eq_single a
        · intro b _ hba
          exact if_neg (fun hb => hba (hunique ω b a hb ha))
        · simp
      _ = p.mass ω := if_pos ha
  · simp only [h, ↓reduceIte]
    symm
    apply Finset.sum_eq_zero
    intro a _
    exact if_neg (fun ha => h ⟨a,ha⟩)
end LooseHamilton
