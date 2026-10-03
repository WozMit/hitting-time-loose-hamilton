module

public import HittingTimeLooseHamilton.RootFreeTestAsymptotic

public section

/-! A registered root test is fixed before the outcome is observed. Only its
bad set may depend on the two root-free graphs. The registry does not range
over those graphs or over all possible functions in the subsequent union bound. -/
noncomputable section
namespace LooseHamilton
open Finset Filter

structure RegisteredRootTest (V : Type*) [Fintype V] [DecidableEq V]
    (r h : ℕ) where
  time : ℕ
  root : V
  prescribed : SimpleHypergraph V
  prescribed_subset : prescribed ⊆ rootEdgeUniverse r root
  prescribed_card : prescribed.card ≤ h
  badSet : SimpleHypergraph V × SimpleHypergraph V → SimpleHypergraph V
  bad_subset : ∀ data, badSet data ⊆ rootEdgeUniverse r root

variable {V : Type*} [Fintype V] [DecidableEq V]

@[expose] def RegisteredRootTest.failure {r h : ℕ} (test : RegisteredRootTest V r h)
    (M : ℕ) (ell : V → ℕ) (c : ℝ)
    (ω : TerminalState V r M ell × MissingOrder V r M) : Prop :=
  M ≤ test.time ∧ test.time ≤ (completeEdges V r).card ∧
    RootFreeTestFailure r M ell test.time test.root test.prescribed test.badSet
      (Fintype.card V) c ω

@[expose] def CommonRootTests {I : Type*} {r h : ℕ}
    (tests : I → RegisteredRootTest V r h) (M : ℕ) (ell : V → ℕ) (c : ℝ)
    (ω : TerminalState V r M ell × MissingOrder V r M) : Prop :=
  ∀ i, ¬ (tests i).failure M ell c ω

/-- One event controls even a subsequently selected label. Selection may use
the observed cut counts: no probability estimate is reapplied after selection. -/
theorem CommonRootTests.selected {I : Type*} {r h M : ℕ} {ell : V → ℕ}
    {tests : I → RegisteredRootTest V r h} {c : ℝ}
    (select : (TerminalState V r M ell × MissingOrder V r M) → I)
    {ω : TerminalState V r M ell × MissingOrder V r M}
    (hω : CommonRootTests tests M ell c ω) :
    ¬ (tests (select ω)).failure M ell c ω := hω (select ω)

/-- The finite union is only over registered labels, not observed root-free
graphs. Its threshold is uniform over all fixed registries of this type. -/
theorem registered_root_union_eventually {r : ℕ} (hr : 3 ≤ r)
    {c : ℝ} (hc : 0 < c) (h : ℕ) :
    ∀ᶠ N in atTop, ∀ (V : Type) [Fintype V] [DecidableEq V], Fintype.card V = N →
      ∀ (M : ℕ) (ell : V → ℕ), [Nonempty (TerminalState V r M ell)] →
      ∀ (I : Type) [Fintype I] (tests : I → RegisteredRootTest V r h),
      (extensionLaw r M ell).event (fun ω => ¬ CommonRootTests tests M ell c ω) ≤
        (Fintype.card I : ℝ) *
          Real.exp (-(c/6400)*FrameScales.L1 N*Real.log (FrameScales.L3 N)) := by
  filter_upwards [root_free_test_probability_eventually hr hc h] with N hN
  intro V _ _ hVN M ell _ I _ tests
  have hi (i : I) : (extensionLaw r M ell).event ((tests i).failure M ell c) ≤
      Real.exp (-(c/6400)*FrameScales.L1 N*Real.log (FrameScales.L3 N)) := by
    by_cases htime : M ≤ (tests i).time ∧ (tests i).time ≤ (completeEdges V r).card
    · have hb := hN V hVN M ell (tests i).time htime.1 htime.2
        (tests i).root (tests i).prescribed (tests i).badSet
        (tests i).prescribed_subset (tests i).prescribed_card (tests i).bad_subset
      apply le_trans _ hb
      apply (extensionLaw r M ell).event_mono
      intro ω hω
      simpa only [hVN] using hω.2.2
    · have he : (tests i).failure M ell c = fun _ => False := by
        funext ω
        apply propext
        simp only [RegisteredRootTest.failure]
        tauto
      rw [he]
      have hz : (extensionLaw r M ell).event (fun _ => False) = 0 := by
        simp [FiniteEntropy.Law.event]
      rw [hz]
      exact (Real.exp_pos _).le
  have he : (fun ω => ¬ CommonRootTests tests M ell c ω) =
      fun ω => ∃ i, (tests i).failure M ell c ω := by
    funext ω
    simp only [CommonRootTests, not_forall, not_not]
  rw [he]
  calc
    _ ≤ ∑ i, (extensionLaw r M ell).event ((tests i).failure M ell c) :=
      (extensionLaw r M ell).finite_union_bound _
    _ ≤ ∑ _i : I, Real.exp (-(c/6400)*FrameScales.L1 N*Real.log (FrameScales.L3 N)) :=
      sum_le_sum (fun i _ => hi i)
    _ = _ := by simp

end LooseHamilton
