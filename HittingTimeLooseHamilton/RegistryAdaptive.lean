module

public import HittingTimeLooseHamilton.RegistryEmbedding

public section

/-! Arbitrary outcome-dependent eligibility and selection do not enlarge the
failure union of a fixed finite registry. No independence of these choices is
assumed or needed. -/
noncomputable section
namespace LooseHamilton
open Filter

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {I : Type*} {r h M : ℕ} {ell : V → ℕ} {c : ℝ}

/-- Some fixed label fails and is deemed eligible after observing the outcome. -/
@[expose] def EligibleRootFailure (tests : I → RegisteredRootTest V r h)
    (eligible : (TerminalState V r M ell × MissingOrder V r M) → I → Prop)
    (c : ℝ) (ω : TerminalState V r M ell × MissingOrder V r M) : Prop :=
  ∃ i, eligible ω i ∧ (tests i).failure M ell c ω

theorem eligibleRootFailure_not_common
    (tests : I → RegisteredRootTest V r h)
    (eligible : (TerminalState V r M ell × MissingOrder V r M) → I → Prop)
    {ω : TerminalState V r M ell × MissingOrder V r M}
    (hω : EligibleRootFailure tests eligible c ω) :
    ¬ CommonRootTests tests M ell c ω := by
  obtain ⟨i, _, hi⟩ := hω
  exact fun hall => hall i hi

theorem CommonRootTests.no_eligible_failure
    {tests : I → RegisteredRootTest V r h}
    (eligible : (TerminalState V r M ell × MissingOrder V r M) → I → Prop)
    {ω : TerminalState V r M ell × MissingOrder V r M}
    (hω : CommonRootTests tests M ell c ω) :
    ¬ EligibleRootFailure tests eligible c ω :=
  fun hbad => eligibleRootFailure_not_common tests eligible hbad hω

/-- Eligibility may include every adaptive gate used by the algorithm. -/
theorem eligibleRootFailure_event_le [Nonempty (TerminalState V r M ell)]
    (tests : I → RegisteredRootTest V r h)
    (eligible : (TerminalState V r M ell × MissingOrder V r M) → I → Prop) :
    (extensionLaw r M ell).event (EligibleRootFailure tests eligible c) ≤
      (extensionLaw r M ell).event (fun ω => ¬ CommonRootTests tests M ell c ω) := by
  apply (extensionLaw r M ell).event_mono
  exact fun _ hω => eligibleRootFailure_not_common tests eligible hω

/-- The selected label and its eligibility may both depend on the full outcome. -/
theorem selectedRootFailure_event_le [Nonempty (TerminalState V r M ell)]
    (tests : I → RegisteredRootTest V r h)
    (eligible : (TerminalState V r M ell × MissingOrder V r M) → I → Prop)
    (select : (TerminalState V r M ell × MissingOrder V r M) → I) :
    (extensionLaw r M ell).event (fun ω =>
      eligible ω (select ω) ∧ (tests (select ω)).failure M ell c ω) ≤
      (extensionLaw r M ell).event (EligibleRootFailure tests eligible c) := by
  apply (extensionLaw r M ell).event_mono
  exact fun ω hω => ⟨select ω, hω⟩

/-- The same uniform threshold controls every possible eligibility rule. -/
theorem eligible_root_union_eventually {r : ℕ} (hr : 3 ≤ r)
    {c : ℝ} (hc : 0 < c) (h : ℕ) :
    ∀ᶠ N in atTop, ∀ (V : Type) [Fintype V] [DecidableEq V], Fintype.card V = N →
      ∀ (M : ℕ) (ell : V → ℕ), [Nonempty (TerminalState V r M ell)] →
      ∀ (I : Type) [Fintype I] (tests : I → RegisteredRootTest V r h)
        (eligible : (TerminalState V r M ell × MissingOrder V r M) → I → Prop),
      (extensionLaw r M ell).event (EligibleRootFailure tests eligible c) ≤
        (Fintype.card I : ℝ) *
          Real.exp (-(c/6400)*FrameScales.L1 N*Real.log (FrameScales.L3 N)) := by
  filter_upwards [registered_root_union_eventually hr hc h] with N hN
  intro V _ _ hVN M ell _ I _ tests eligible
  exact le_trans (eligibleRootFailure_event_le tests eligible)
    (hN V hVN M ell I tests)

/-- In particular an arbitrary eligible adaptive selection incurs no extra
union-bound factor beyond the number of fixed labels. -/
theorem selected_root_failure_eventually {r : ℕ} (hr : 3 ≤ r)
    {c : ℝ} (hc : 0 < c) (h : ℕ) :
    ∀ᶠ N in atTop, ∀ (V : Type) [Fintype V] [DecidableEq V], Fintype.card V = N →
      ∀ (M : ℕ) (ell : V → ℕ), [Nonempty (TerminalState V r M ell)] →
      ∀ (I : Type) [Fintype I] (tests : I → RegisteredRootTest V r h)
        (eligible : (TerminalState V r M ell × MissingOrder V r M) → I → Prop)
        (select : (TerminalState V r M ell × MissingOrder V r M) → I),
      (extensionLaw r M ell).event (fun ω =>
        eligible ω (select ω) ∧ (tests (select ω)).failure M ell c ω) ≤
        (Fintype.card I : ℝ) *
          Real.exp (-(c/6400)*FrameScales.L1 N*Real.log (FrameScales.L3 N)) := by
  filter_upwards [eligible_root_union_eventually hr hc h] with N hN
  intro V _ _ hVN M ell _ I _ tests eligible select
  exact le_trans (selectedRootFailure_event_le tests eligible select)
    (hN V hVN M ell I tests eligible)

end LooseHamilton
