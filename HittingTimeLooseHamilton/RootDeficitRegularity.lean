module

public import HittingTimeLooseHamilton.TerminalRegularity
public import HittingTimeLooseHamilton.BoundaryDeficit
public import HittingTimeLooseHamilton.RootLinkDeficit

public section

/-! Terminal regularity supplies the single-root feasibility gate used by
root-free sampling. No additional probabilistic event is required. -/
noncomputable section
namespace LooseHamilton
open Finset
open scoped BigOperators
variable {V : Type} [Fintype V] [DecidableEq V]

omit [Fintype V] in
/-- Removing all root edges agrees with the ambient-label surviving host. -/
theorem survivingHost_singleton_eq_rootFreeEdges (F : SimpleHypergraph V) (y : V) :
    survivingHost F {y} = rootFreeEdges y F := by
  ext e
  simp [survivingHost,rootFreeEdges]

/-- The non-root deficit in the root-link model is exactly the deficit after
inducing on the complement of the root vertex. -/
theorem rootAdjustedDeficit_sum_eq_terminalDeletionDeficit
    (F : SimpleHypergraph V) (ell : V → ℕ) (y : V) :
    (∑ v, rootAdjustedDeficit y ell (rootFreeEdges y F) v) =
      terminalDeletionDeficit F ell {y} := by
  classical
  rw [terminalDeletionDeficit_eq_ambient_sum,
    survivingHost_singleton_eq_rootFreeEdges]
  have hs : (univ : Finset V) \ {y} = univ.filter (fun v => v ≠ y) := by
    ext v
    simp
  rw [hs,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro v _
  by_cases hv : v = y <;> simp [rootAdjustedDeficit,hv]

/-- A threshold depending only on fixed parameters makes every root deficit
at most one on the existing terminal-regularity event, simultaneously for all
admissible terminal data, terminal states and roots. -/
theorem eventually_regular_root_deficit (r : ℕ) (C offset : ℝ) :
    ∃ N₀ : ℕ, ∀ (V : Type) [Fintype V] [DecidableEq V], N₀ ≤ Fintype.card V →
      ∀ (M : ℕ) (ell : V → ℕ) (original : Finset (Finset V)),
      CoreAdmissible r M ell original offset → ∀ F : TerminalState V r M ell,
      TerminalRegular C F.val → ∀ y : V,
        (∑ v, rootAdjustedDeficit y ell (rootFreeEdges y F.val) v) ≤ 1 := by
  obtain ⟨N₀,hN₀⟩ := terminal_deficit_bound r C offset 1
  refine ⟨N₀,?_⟩
  intro V _ _ hN M ell original admissible F hF y
  rw [rootAdjustedDeficit_sum_eq_terminalDeletionDeficit]
  simpa only [Finset.card_singleton] using
    hN₀ V hN M ell original admissible F hF {y} (by simp)

end LooseHamilton
