module

public import HittingTimeLooseHamilton.TerminalRegularityModels

public section

/-! The exact quantifiers of Proposition 4.3 of the supplied manuscript. -/
noncomputable section
namespace LooseHamilton

/-- Uniform high probability under the existing conditioned terminal law.
The cutoff is independent of the marked matching, M, and the offset function. -/
@[expose] def TerminalRegularityWhp (r : ℕ) (C B : ℝ) : Prop :=
  ∀ η : ℝ, 0 < η → ∃ N₀ : ℕ,
    ∀ (V : Type) [Fintype V] [DecidableEq V], N₀ ≤ Fintype.card V →
      ∀ (M : ℕ) (ell : V → ℕ) (markers : Finset (Finset V)),
        ∀ hadm : CoreAdmissible r M ell markers B,
        letI : Nonempty (TerminalState V r M ell) := hadm.feasible
        1-η ≤ (terminalLaw r M ell).event (fun F => TerminalRegular C F.val)

/-- On the same regularity event, every deletion of at most the fixed h vertices
has total positive degree deficit at most its number of deleted vertices. -/
@[expose] def TerminalDeficitBound (r : ℕ) (C B : ℝ) (h : ℕ) : Prop :=
  ∃ N₀ : ℕ, ∀ (V : Type) [Fintype V] [DecidableEq V], N₀ ≤ Fintype.card V →
    ∀ (M : ℕ) (ell : V → ℕ) (markers : Finset (Finset V)),
      CoreAdmissible r M ell markers B → ∀ F : TerminalState V r M ell,
        TerminalRegular C F.val → ∀ Z : Finset V, Z.card ≤ h →
          terminalDeletionDeficit F.val ell Z ≤ Z.card

/-- Proposition 4.3: terminal regularity and finite-deletion deficit.
C may depend only on the fixed r. Offset bounds are fixed in advance; for every
fixed h the deficit clause holds on the regularity event for all sufficiently
large N. It makes no assertion simultaneously for unbounded h. -/
@[expose] def Proposition43 : Prop :=
  ∀ r : ℕ, 3 ≤ r → ∃ C : ℝ, 0 < C ∧ ∀ B : ℝ, 0 ≤ B →
    TerminalRegularityWhp r C B ∧ ∀ h : ℕ, TerminalDeficitBound r C B h
end LooseHamilton
