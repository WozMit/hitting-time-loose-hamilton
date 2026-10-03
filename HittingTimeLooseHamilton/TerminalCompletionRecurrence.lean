module

public import HittingTimeLooseHamilton.TerminalCompletionCount
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

public section

/-! The completion-count recurrence behind the next-deletion kernel. -/
noncomputable section
namespace LooseHamilton
open Finset
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Every feasible terminal subgraph is counted once for each deletable edge
of the current graph outside that terminal subgraph. -/
theorem terminalCompletionCount_erase_sum (r M : ℕ) (ell : V → ℕ)
    (H : SimpleHypergraph V) :
    ∑ e ∈ H, terminalCompletionCount r M ell (H.erase e) =
      (H.card-M)*terminalCompletionCount r M ell H := by
  classical
  simp only [terminalCompletionCount,Finset.card_eq_sum_ones,Finset.sum_filter]
  rw [Finset.sum_comm]
  have hs : ∀ F : TerminalState V r M ell,
      (∑ e ∈ H, if F.val ⊆ H.erase e then 1 else 0) =
        if F.val ⊆ H then H.card-M else 0 := by
    intro F
    simp only [subset_erase]
    by_cases hF : F.val ⊆ H
    · simp only [hF,true_and]
      have hc : H.filter (fun e => e ∉ F.val) = H \ F.val := by ext e; simp
      rw [← Finset.sum_filter,← Finset.card_eq_sum_ones,hc,card_sdiff_of_subset hF,F.property.2.1]
      simp
    · simp [hF]
  simp_rw [hs]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro F _
  split_ifs <;> simp

/-- The displayed next-deletion weights sum to one over the current edges. -/
theorem terminalCompletionCount_kernel_sum (r M : ℕ) (ell : V → ℕ)
    (H : SimpleHypergraph V) (hM : M < H.card)
    (hZ : 0 < terminalCompletionCount r M ell H) :
    ∑ e ∈ H, (terminalCompletionCount r M ell (H.erase e):ℝ) /
      ((H.card-M:ℕ)*(terminalCompletionCount r M ell H:ℝ)) = 1 := by
  rw [← Finset.sum_div]
  have hs : (∑ e ∈ H, (terminalCompletionCount r M ell (H.erase e):ℝ)) =
      ((H.card-M:ℕ):ℝ)*(terminalCompletionCount r M ell H:ℝ) := by
    exact_mod_cast terminalCompletionCount_erase_sum r M ell H
  rw [hs]
  apply div_self
  apply mul_ne_zero
  · exact_mod_cast Nat.ne_of_gt (Nat.sub_pos_of_lt hM)
  · exact_mod_cast Nat.ne_of_gt hZ
end LooseHamilton
