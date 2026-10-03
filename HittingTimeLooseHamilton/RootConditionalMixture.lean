module

public import HittingTimeLooseHamilton.CoreConditionalCounting
public import Mathlib.Tactic

public section

/-! Removing a finite auxiliary exposure by averaging positive conditional fibres. -/
noncomputable section
namespace LooseHamilton
open Finset
open scoped BigOperators
variable {Ω I : Type*} [Fintype Ω] [Fintype I]

lemma event_eq_sum_observation_fibres (p : FiniteEntropy.Law Ω)
    (E : Ω → Prop) (f : Ω → I) :
    p.event E = ∑ i, p.event (fun ω => E ω ∧ f ω = i) := by
  classical
  have he : E = (fun ω => ∃ i, E ω ∧ f ω = i) := by
    funext ω
    apply propext
    simp
  rw [he]
  convert event_exists_eq_sum p (fun i ω => E ω ∧ f ω = i) (by
    intro ω i j hi hj
    exact hi.2.symm.trans hj.2) using 1
  congr 1
  funext i
  congr 1
  funext ω
  apply propext
  simp

/-- A weighted bound also valid when some observation fibres have zero mass.
No sign assumption is needed on the fibre bounds. -/
theorem joint_event_le_sum_conditional_bounds (p : FiniteEntropy.Law Ω)
    (E Bad : Ω → Prop) (f : Ω → I) (γ : I → ℝ)
    (hbound : ∀ i (hi : 0 < p.event (fun ω => E ω ∧ f ω = i)),
      (p.condition (fun ω => E ω ∧ f ω = i) hi).event Bad ≤ γ i) :
    p.event (fun ω => E ω ∧ Bad ω) ≤
      ∑ i, γ i * p.event (fun ω => E ω ∧ f ω = i) := by
  classical
  rw [event_eq_sum_observation_fibres p (fun ω => E ω ∧ Bad ω) f]
  apply sum_le_sum
  intro i _
  have he : p.event (fun ω => (E ω ∧ Bad ω) ∧ f ω = i) =
      p.event (fun ω => (E ω ∧ f ω = i) ∧ Bad ω) := by
    congr 1
    funext ω
    exact propext (by tauto)
  rw [he]
  by_cases hi : 0 < p.event (fun ω => E ω ∧ f ω = i)
  · have hb := hbound i hi
    rw [condition_event_eq_joint] at hb
    exact (div_le_iff₀ hi).mp hb
  · have hz : p.event (fun ω => E ω ∧ f ω = i) = 0 :=
      le_antisymm (le_of_not_gt hi) (p.event_nonneg _)
    rw [hz,mul_zero]
    exact (p.event_mono (fun ω h => h.1)).trans_eq hz

/-- A common conditional bound on every positive refined fibre remains valid
when the finite observation is forgotten. -/
theorem conditional_event_le_of_fibre_bounds (p : FiniteEntropy.Law Ω)
    (E Bad : Ω → Prop) (f : Ω → I) (hE : 0 < p.event E) (γ : ℝ)
    (hbound : ∀ i (hi : 0 < p.event (fun ω => E ω ∧ f ω = i)),
      (p.condition (fun ω => E ω ∧ f ω = i) hi).event Bad ≤ γ) :
    (p.condition E hE).event Bad ≤ γ := by
  classical
  rw [condition_event_eq_joint]
  apply (div_le_iff₀ hE).mpr
  have hb := joint_event_le_sum_conditional_bounds p E Bad f (fun _ => γ) hbound
  rw [←mul_sum,←event_eq_sum_observation_fibres p E f] at hb
  exact hb

/-- The corresponding unconditioned mixture estimate. -/
theorem event_le_of_observation_conditional_bounds (p : FiniteEntropy.Law Ω)
    (Bad : Ω → Prop) (f : Ω → I) (γ : ℝ)
    (hbound : ∀ i (hi : 0 < p.event (fun ω => f ω = i)),
      (p.condition (fun ω => f ω = i) hi).event Bad ≤ γ) :
    p.event Bad ≤ γ := by
  have hb := joint_event_le_sum_conditional_bounds p (fun _ => True) Bad f (fun _ => γ)
    (by simpa only [true_and] using hbound)
  simp only [true_and] at hb
  have hs := event_eq_sum_observation_fibres p (fun _ => True) f
  simp only [true_and] at hs
  rw [←mul_sum,←hs] at hb
  simpa using hb
end LooseHamilton
