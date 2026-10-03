module

public import HittingTimeLooseHamilton.CandidateExperiment
public import HittingTimeLooseHamilton.TerminalRegularityModels
public import HittingTimeLooseHamilton.PathRegularityModels

public section

/-! Item 30.2: statement of the repaired `Uniform candidate balance` target
(manuscript label `prop:candidates`, formerly Proposition 8.1).
`UniformCandidateBalance` is a proposition DEFINITION, not a proved theorem.
All scales use the original N. Counts and legal roles are the actual labelled
frame counts, with all prescribed directions and the original prohibition. -/
noncomputable section
namespace LooseHamilton.CandidateBalance
open Finset AuxiliaryFrame
variable {V : Type} [Fintype V] [DecidableEq V]
variable {r M : ℕ} {ell : V → ℕ} {original : Finset (Finset V)}
attribute [local instance] Classical.propDecidable

/-- Inherited regularity at the specified time, from terminal regularity and
path regularity with its bounded-deletion and fixed-prohibition variants.
There is no assumption about unrelated times and no new offset assumption after
boundary exposure. The original terminal graph is retained in this predicate. -/
@[expose] def InheritedRegularity (original : Finset (Finset V)) (j h : ℕ)
    (c C L : ℝ) (ω : Outcome V r M ell) : Prop :=
  TerminalRegular C ω.1.val ∧
  PathGraphRegular r c C L (extensionState ω.1 ω.2 j) ∧
  (∀ Z : Finset V, Z.card ≤ h →
    PathGraphRegular r c C L (deleteVertices Z (extensionState ω.1 ω.2 j))) ∧
  (∀ Z : Finset V, Z.card ≤ h →
    PathGraphUpperRegular r C L
      (fixedPortHost (deleteVertices Z (extensionState ω.1 ω.2 j))
        (restrictedPorts (univ \ Z) (originalPorts original))))

/-- The three events in the printed statement are intersected, not conditioned on. -/
@[expose] def BadSource (f : Frame r original) (j h : ℕ) (c C L B : ℝ)
    (ω : Outcome V r M ell) : Prop :=
  InheritedRegularity original j h c C L ω ∧
  f.entropyBudget (extensionState ω.1 ω.2 j) B ∧
  f.candidateBadAtScale (extensionState ω.1 ω.2 j)

/-- Explicit audit: both badness comparisons are strict, the denominator counts
ALL legal directed candidates, and the budget uses original N, not active n_f.
The positive cycle count makes the logarithmic entropy budget meaningful. -/
theorem badSource_iff (f : Frame r original) (j h : ℕ) (c C L B : ℝ)
    (ω : Outcome V r M ell) :
    BadSource f j h c C L B ω ↔
      InheritedRegularity original j h c C L ω ∧
      (0 < f.cycleCount (extensionState ω.1 ω.2 j) ∧
       (f.k:ℝ)*Real.log (((r:ℝ)-1)*f.mu (extensionState ω.1 ω.2 j)) -
        ((r:ℝ)-1)*f.k - B*(Fintype.card V:ℝ)/Real.sqrt (FrameScales.L1 (Fintype.card V))
        ≤ Real.log (f.cycleCount (extensionState ω.1 ω.2 j))) ∧
      FrameScales.alpha (Fintype.card V)*(f.candidates.card:ℝ) <
        ((f.candidates.filter (fun a =>
          |(f.completionCount (extensionState ω.1 ω.2 j) a:ℝ) /
            ((f.cycleCount (extensionState ω.1 ω.2 j):ℝ) /
              (((r:ℝ)-1)^2*f.mu (extensionState ω.1 ω.2 j))) - 1| >
                FrameScales.alpha (Fintype.card V))).card:ℝ) := by
  simp only [BadSource, Frame.entropyBudget_iff, Frame.candidateBadAtScale,
    Frame.candidateBad]

/-- Existing path events imply this fixed-time inherited event. This bridge uses
only definitions and previously compiled regularity predicates. -/
theorem inherited_of_path (j h : ℕ) (c C L : ℝ) (ω : Outcome V r M ell)
    (hj : M ≤ j) (hK : j ≤ (completeEdges V r).card)
    (ht : TerminalRegular C ω.1.val)
    (hp : PathRegularityEvent r M ell c C L ω)
    (hd : PathDeletionRegularityEvent r M ell h c C L ω)
    (hf : PathProhibitionRegularityEvent r M ell original h C L ω) :
    InheritedRegularity original j h c C L ω :=
  ⟨ht, hp j hj hK, hd j hj hK, hf j hj hK⟩

/-- The exact requested exponential scale. -/
@[expose] def errorBound (N : ℕ) (rate : ℝ) : ℝ :=
  Real.exp (-rate * FrameScales.L1 N * (FrameScales.L3 N)^(99/100:ℝ))

/-- Both the unconditional and every positive-probability fixed bounded-boundary
version. Boundary vertices need not be deleted from the frame. Compatibility
with regularity is enforced inside BadSource, never by conditioning on it. -/
@[expose] def FixedFrameBound [Nonempty (TerminalState V r M ell)]
    (f : Frame r original) (j h boundaryBound : ℕ) (c C L B rate : ℝ) : Prop :=
  (extensionLaw r M ell).event (BadSource f j h c C L B) ≤
    errorBound (Fintype.card V) rate ∧
  ∀ b : BoundaryRecord V, b.vertices.card ≤ boundaryBound →
    ∀ hb : b.Feasible (r:=r) (M:=M) (ell:=ell) j,
      (b.law j hb).event (BadSource f j h c C L B) ≤
        errorBound (Fintype.card V) rate

/-- Uniform asymptotic target. Rate depends only on r. The threshold may depend
on the fixed budget, offset, regularity and boundary constants, and is chosen
BEFORE N, terminal parameters, original markers, labelled frame, time and record.
This is only the specification for item 30.19; it does not assert the estimate. -/
@[expose] def UniformCandidateBalance : Prop :=
  ∀ r : ℕ, 3 ≤ r → ∃ rate : ℝ, 0 < rate ∧
    ∀ B offset c C L : ℝ, 0 ≤ B → 0 ≤ offset → 0 < c → 0 < C → 0 < L →
    ∀ h boundaryBound : ℕ, 4*r ≤ h → ∃ N₀ : ℕ,
      ∀ N : ℕ, N₀ ≤ N → ∀ M : ℕ, ∀ ell : Fin N → ℕ,
      ∀ original : Finset (Finset (Fin N)),
      ∀ admissible : CoreAdmissible r M ell original offset,
      ∀ f : Frame r original, ∀ j : ℕ,
        M ≤ j → j ≤ (completeEdges (Fin N) r).card →
        @FixedFrameBound (Fin N) _ _ r M ell original admissible.feasible
          f j h boundaryBound c C L B rate

end LooseHamilton.CandidateBalance
