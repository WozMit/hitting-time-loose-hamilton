module

public import HittingTimeLooseHamilton.MissingBoundaryKernel
public import HittingTimeLooseHamilton.TerminalCompletionCount
public import HittingTimeLooseHamilton.KahnRandomOrder

public section

/-! Joint current-state and next-deletion probabilities under the actual extension law. -/
noncomputable section
namespace LooseHamilton
open Finset
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]

lemma extension_boundary_completion_probability (r M : ℕ) (ell : V → ℕ)
    [Nonempty (TerminalState V r M ell)]
    (j : ℕ) (hMj : M<j) (hj : j ≤ (completeEdges V r).card)
    (H : SimpleHypergraph V) (hH : H ⊆ completeEdges V r) (hHj : H.card=j)
    (e : Finset V) (he : e∈H) :
    (extensionLaw r M ell).event (fun ω =>
      extensionState ω.1 ω.2 j=H ∧ extensionState ω.1 ω.2 (j-1)=H.erase e) =
        (terminalCompletionCount r M ell (H.erase e):ℝ) /
          ((Fintype.card (TerminalState V r M ell):ℝ)*
            ((j-M:ℕ):ℝ)*(((completeEdges V r).card-M).choose (j-M):ℝ)) := by
  classical
  rw [extensionLaw,FiniteEntropy.Law.event_prod_sum]
  simp_rw [extension_boundary_kernel _ j hMj hj H hH hHj e he]
  simp only [terminalLaw_mass]
  have hsum : (∑ F : TerminalState V r M ell,
      (1/(Fintype.card (TerminalState V r M ell):ℝ))*
        (if F.val ⊆ H.erase e then
          1/(((j-M:ℕ):ℝ)*(((completeEdges V r).card-M).choose (j-M):ℝ)) else 0)) =
      ∑ F ∈ (univ : Finset (TerminalState V r M ell)).filter (fun F => F.val ⊆ H.erase e),
        (1/(Fintype.card (TerminalState V r M ell):ℝ))*
          (1/(((j-M:ℕ):ℝ)*(((completeEdges V r).card-M).choose (j-M):ℝ))) := by
    rw [sum_filter]
    apply sum_congr rfl
    intro F _
    split_ifs <;> simp
  rw [hsum,sum_const,nsmul_eq_mul]
  change (terminalCompletionCount r M ell (H.erase e):ℝ)*_=_
  ring
end LooseHamilton
