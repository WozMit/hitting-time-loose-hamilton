module

public import HittingTimeLooseHamilton.ConditionedPath
public import HittingTimeLooseHamilton.StoppedCountingStatement

public section

/-! Exact whole-path transport between the actual extension law and the
terminal-conditioned uniform deletion law on the complete-edge ground type. -/
noncomputable section
namespace LooseHamilton.FirstFailurePathLaw
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V] {r : ℕ}

@[expose] def host (S : Finset (Edge V r)) : SimpleHypergraph V := S.image Subtype.val

@[expose] def terminalDegree (ell : V → ℕ) (S : Finset (Edge V r)) : Prop :=
  ∀ v, ell v ≤ vertexDegree (host S) v

@[simp] theorem host_rank_prefix (σ : EdgeOrder V r) (j : ℕ) :
    host (orderPrefix (orderRankEquiv (Edge V r) σ) j) = processState σ j := by
  rfl

/-- Uniform edge permutations and uniform rank bijections give identical path events. -/
theorem process_path_event_eq_deletion (P : (ℕ → SimpleHypergraph V) → Prop) :
    (processLaw V r).event (fun σ => P (processState σ)) =
      (StoppedCounting.deletionLaw (Edge V r)).event
        (fun ρ => P (fun j => host (orderPrefix ρ j))) := by
  classical
  letI : Nonempty (FiniteOrder (Edge V r)) := ⟨Fintype.equivFin _⟩
  exact FiniteEntropy.Law.uniform_event_equiv (orderRankEquiv (Edge V r))
    (fun ρ => P (fun j => host (orderPrefix ρ j)))

/-- The conditioning probability is exactly the previously defined feasibility beta. -/
theorem terminal_event_eq_beta (M : ℕ) (ell : V → ℕ) :
    (StoppedCounting.deletionLaw (Edge V r)).event
      (StoppedCounting.terminalEvent M (terminalDegree ell)) =
      terminalFeasibilityProbability r M ell := by
  symm
  exact process_path_event_eq_deletion (fun H => ∀ v, ell v ≤ vertexDegree (H M) v)

theorem terminal_event_pos (M : ℕ) (ell : V → ℕ)
    [Nonempty (TerminalState V r M ell)] :
    0 < (StoppedCounting.deletionLaw (Edge V r)).event
      (StoppedCounting.terminalEvent M (terminalDegree ell)) := by
  rw [terminal_event_eq_beta]
  exact terminalFeasibilityProbability_pos r M ell

/-- Exact equality for arbitrary events of the entire size-indexed host path.
The rank path is clamped below the terminal size, exactly as extensionState is. -/
theorem extension_event_eq_conditioned_deletion (M : ℕ) (ell : V → ℕ)
    [Nonempty (TerminalState V r M ell)] (P : (ℕ → SimpleHypergraph V) → Prop) :
    (extensionLaw r M ell).event (fun ω => P (extensionState ω.1 ω.2)) =
      ((StoppedCounting.deletionLaw (Edge V r)).condition
        (StoppedCounting.terminalEvent M (terminalDegree ell)) (terminal_event_pos M ell)).event
        (fun ρ => P (fun j => host (orderPrefix ρ (max M j)))) := by
  classical
  rw [extension_path_event_eq_conditioned, condition_event_eq_joint]
  rw [terminal_event_eq_beta]
  congr 1
  exact process_path_event_eq_deletion
    (fun H => (∀ v, ell v ≤ vertexDegree (H M) v) ∧ P (fun j => H (max M j)))

/-- Events using only sizes at or above M need no clamping on the deletion side. -/
theorem extension_event_eq_conditioned_deletion_of_local (M : ℕ) (ell : V → ℕ)
    [Nonempty (TerminalState V r M ell)] (P : (ℕ → SimpleHypergraph V) → Prop)
    (hP : ∀ H H' : ℕ → SimpleHypergraph V,
      (∀ j, M ≤ j → H j = H' j) → (P H ↔ P H')) :
    (extensionLaw r M ell).event (fun ω => P (extensionState ω.1 ω.2)) =
      ((StoppedCounting.deletionLaw (Edge V r)).condition
        (StoppedCounting.terminalEvent M (terminalDegree ell)) (terminal_event_pos M ell)).event
        (fun ρ => P (fun j => host (orderPrefix ρ j))) := by
  rw [extension_event_eq_conditioned_deletion]
  congr 1
  funext ρ
  apply propext
  exact hP _ _ (fun j hj => by rw [max_eq_right hj])

/-- Whole-path conditioning costs beta inverse, with no union over times. -/
theorem extension_event_le_deletion_div (M : ℕ) (ell : V → ℕ)
    [Nonempty (TerminalState V r M ell)] (P : (ℕ → SimpleHypergraph V) → Prop) :
    (extensionLaw r M ell).event (fun ω => P (extensionState ω.1 ω.2)) ≤
      (StoppedCounting.deletionLaw (Edge V r)).event
        (fun ρ => P (fun j => host (orderPrefix ρ (max M j)))) /
        terminalFeasibilityProbability r M ell := by
  rw [extension_event_eq_conditioned_deletion]
  have h := StoppedCounting.conditional_event_le
    (StoppedCounting.deletionLaw (Edge V r))
    (StoppedCounting.terminalEvent M (terminalDegree ell))
    (fun ρ => P (fun j => host (orderPrefix ρ (max M j)))) (terminal_event_pos M ell)
  rw [terminal_event_eq_beta] at h
  simpa only [div_eq_mul_inv, mul_comm] using h

end LooseHamilton.FirstFailurePathLaw
