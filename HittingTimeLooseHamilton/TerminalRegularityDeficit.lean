module

public import HittingTimeLooseHamilton.TerminalRegularityModels
public import HittingTimeLooseHamilton.TerminalDeletionInduced

public section

noncomputable section
namespace LooseHamilton
open Finset Filter
open scoped BigOperators

/-- Fixed offsets and a fixed deletion bound are eventually absorbed by the
slack between epsilon log N and 3 epsilon log N. -/
theorem eventually_terminal_deletion_slack (B : ℝ) (h : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ ell : ℕ,
      |(ell : ℝ) - Nat.floor (epsilon * Real.log n)| ≤ B →
      (ell + 2 * h : ℕ) ≤ (3 * epsilon * Real.log n : ℝ) := by
  have hlog : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  filter_upwards [hlog.eventually (eventually_ge_atTop (max 0 (50*(B+2*h))))] with n hn
  have hn0 : 0 ≤ Real.log (n : ℝ) := (le_max_left _ _).trans hn
  have hnB : 50*(B+2*h) ≤ Real.log (n : ℝ) := (le_max_right _ _).trans hn
  intro ell he
  have hf : (Nat.floor (epsilon * Real.log (n : ℝ)) : ℝ) ≤
      epsilon * Real.log n := Nat.floor_le (by unfold epsilon; positivity)
  have he' := (abs_le.mp he).2
  push_cast
  unfold epsilon at *
  linarith

/-- The deterministic clause of Proposition 4.3 holds on precisely the stated
terminal regularity event, uniformly over all bounded vertex deletions. -/
theorem eventually_terminal_regular_deficit (B C : ℝ) (h : ℕ) :
    ∀ᶠ n : ℕ in atTop,
      ∀ (V : Type*) [Fintype V] [DecidableEq V], Fintype.card V = n →
      ∀ (r M : ℕ) (ell : V → ℕ) (markers : Finset (Finset V)),
      CoreAdmissible r M ell markers B →
      ∀ F : TerminalState V r M ell, TerminalRegular C F.val →
      ∀ Z : Finset V, Z.card ≤ h → terminalDeletionDeficit F.val ell Z ≤ Z.card := by
  filter_upwards [eventually_terminal_deletion_slack B h] with n hn
  intro V _ _ hV r M ell markers hadm F hF Z hZ
  apply terminal_induced_deletion_deficit_of_threshold F.val ell
    (3 * epsilon * Real.log (Fintype.card V : ℝ)) h
    F.property.2.2 _ hF.pair_degree hF.low_stars Z hZ
  intro v
  rw [hV]
  apply hn (ell v)
  simpa only [lowerDegreeBase, hV] using hadm.offsets v

end LooseHamilton
