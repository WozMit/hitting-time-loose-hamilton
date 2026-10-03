module

public import HittingTimeLooseHamilton.PathIncidenceConditional

public section

/-! Vanishing failure probability for all degree and codegree path bounds under Q. -/
noncomputable section
namespace LooseHamilton
open Filter

lemma path_incidence_failure_eventually (r : ℕ) (hr : 3 ≤ r) (B : ℝ) (hB : 0 ≤ B) :
    ∀ᶠ n : ℕ in atTop, ∀ (V : Type) [Fintype V] [DecidableEq V], Fintype.card V=n →
      ∀ (M : ℕ) (ell : V → ℕ) (markers : Finset (Finset V)),
        (hadm : CoreAdmissible r M ell markers B) →
        letI := hadm.feasible
        (extensionLaw r M ell).event (fun ω =>
          ∃ j : ℕ, M ≤ j ∧ j ≤ (completeEdges V r).card ∧
            ¬PathIncidenceRegular r (pathDegreeLowerFactor r)
              (pathDegreeUpperFactor r terminalRegularityConstant) 4
                (extensionState ω.1 ω.2 j)) ≤ pathIncidenceError r n := by
  filter_upwards [path_incidence_conditional_eventually r hr B,
    terminal_regular_failure_eventually r hr B hB] with n hc ht
  intro V _ _ hcard M ell markers hadm
  letI := hadm.feasible
  have hm := extension_bad_event_le_terminal_plus r M ell
    (fun F σ => ∃ j : ℕ, M ≤ j ∧ j ≤ (completeEdges V r).card ∧
      ¬PathIncidenceRegular r (pathDegreeLowerFactor r)
        (pathDegreeUpperFactor r terminalRegularityConstant) 4 (extensionState F σ j))
    (6*(n:ℝ)^(-3:ℝ)) (by positivity) (hc V hcard M ell markers hadm)
  have hh := ht V hcard M ell markers hadm
  exact hm.trans (add_le_add_left hh _)
end LooseHamilton
