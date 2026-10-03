module

public import HittingTimeLooseHamilton.KahnRandomOrder
public import Mathlib.Tactic

public section
noncomputable section
namespace LooseHamilton
open Finset
attribute [local instance] Classical.propDecidable

/-- A uniform finite distribution inherits any bound valid on every occupied fiber. -/
theorem uniform_event_le_of_fibers {Ω ι : Type*} [Fintype Ω] [Nonempty Ω]
    [Fintype ι] [DecidableEq ι] (f : Ω → ι) (P : Ω → Prop) (b : ℝ)
    (h : ∀ i, ∀ [Nonempty {ω : Ω // f ω = i}],
      (FiniteEntropy.uniform : FiniteEntropy.Law {ω : Ω // f ω = i}).event
        (fun ω => P ω.val) ≤ b) :
    (FiniteEntropy.uniform : FiniteEntropy.Law Ω).event P ≤ b := by
  classical
  have hc (i : ι) :
      (∑ ω : {ω : Ω // f ω = i}, if P ω.val then (1:ℝ) else 0) ≤
      (Fintype.card {ω : Ω // f ω = i} : ℝ)*b := by
    by_cases hn : Nonempty {ω : Ω // f ω = i}
    · letI := hn
      have hi := h i
      rw [FiniteEntropy.Law.uniform_event] at hi
      have hp : (0:ℝ) < Fintype.card {ω : Ω // f ω = i} := by
        exact_mod_cast Fintype.card_pos
      have hi' := (div_le_iff₀ hp).mp hi
      simpa [← sum_filter,mul_comm] using hi'
    · haveI : IsEmpty {ω : Ω // f ω = i} := not_nonempty_iff.mp hn
      simp
  have hs := sum_le_sum (fun i (_ : i ∈ (univ : Finset ι)) => hc i)
  rw [Fintype.sum_fiberwise f (fun ω => if P ω then (1:ℝ) else 0)] at hs
  have hcard : (∑ i, (Fintype.card {ω : Ω // f ω = i} : ℝ)) = Fintype.card Ω := by
    simp only [← Nat.cast_sum]
    congr 1
    simpa only [Fintype.card_sigma] using Fintype.card_congr (Equiv.sigmaFiberEquiv f)
  rw [← sum_mul,hcard] at hs
  rw [FiniteEntropy.Law.uniform_event]
  apply (div_le_iff₀ (by exact_mod_cast Fintype.card_pos (α:=Ω))).mpr
  simpa [← sum_filter,mul_comm] using hs
end LooseHamilton
