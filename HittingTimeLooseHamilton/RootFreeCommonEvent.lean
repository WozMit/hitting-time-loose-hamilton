module

public import HittingTimeLooseHamilton.CommonRootEvent
public import HittingTimeLooseHamilton.CandidateBalanceCommonEvent
public import HittingTimeLooseHamilton.CommonRegularityEvent
public import HittingTimeLooseHamilton.RootDeficitRegularity

public section

/-! # Section 10: the common high-probability event

The terminal/path regularity event is intersected once. Candidate and root-link
tests are separately registered over polynomial label families. The common
event is under the original extension law, without conditioning on regularity,
the entropy budget, the density gate, or a selected cut. -/
noncomputable section
namespace LooseHamilton
open Finset RootFreeTestIndexing CandidateBalance

variable {N r M hR : ℕ} {ell : Fin N → ℕ}
variable {original : Finset (Finset (Fin N))}

@[expose] def RootFreeCommonEvent
    (tests : RootTestIndex r original → RegisteredRootTest (Fin N) r hR)
    (h : ℕ) (c C L B cRoot : ℝ) (ω : Outcome (Fin N) r M ell) : Prop :=
  CommonRegularity r M ell original h c C L ω ∧
  CommonCandidateBalance original h c C L B ω ∧
  CommonRootTests tests M ell cRoot ω ∧
  ∀ y : Fin N, (∑ v, rootAdjustedDeficit y ell (rootFreeEdges y ω.1.val) v) ≤ 1

/-- On the common event the regularity antecedent of candidate balance is
already satisfied. The entropy budget is retained as the required hypothesis. -/
theorem RootFreeCommonEvent.candidates
    {tests : RootTestIndex r original → RegisteredRootTest (Fin N) r hR}
    {h : ℕ} {c C L B cRoot : ℝ} {ω : Outcome (Fin N) r M ell}
    (hω : RootFreeCommonEvent tests h c C L B cRoot ω)
    (f : AuxiliaryFrame.Frame r original) (j : ℕ)
    (hj : M ≤ j) (hK : j ≤ (completeEdges (Fin N) r).card)
    (hb : f.entropyBudget (extensionState ω.1 ω.2 j) B) :
    ¬ f.candidateBadAtScale (extensionState ω.1 ω.2 j) :=
  hω.2.1 f j hj hK (hω.1.inherited hj hK) hb

/-- A registered root link passes its sampling test whenever its prescribed
edges, logarithmic degree and density hypotheses hold. The root deficit is
derived from terminal regularity and is no longer a user-supplied hypothesis. -/
theorem RootFreeCommonEvent.root_test
    {tests : RootTestIndex r original → RegisteredRootTest (Fin N) r hR}
    {h : ℕ} {c C L B cRoot : ℝ} {ω : Outcome (Fin N) r M ell}
    (hω : RootFreeCommonEvent tests h c C L B cRoot ω)
    (i : RootTestIndex r original)
    (hj : M ≤ (tests i).time) (hK : (tests i).time ≤ (completeEdges (Fin N) r).card)
    (hR : (tests i).prescribed ⊆ (rootSamplingPair r M ell (tests i).time ω).2)
    (hdegree : cRoot*FrameScales.L1 (Fintype.card (Fin N)) ≤
      (((tests i).time-(rootFreePairObservation r M ell (tests i).time (tests i).root ω).2.card : ℕ) : ℝ))
    (hdensity : rootLinkDensity r (tests i).root
      ((tests i).badSet (rootFreePairObservation r M ell (tests i).time (tests i).root ω)) ≤
        FrameScales.rho (Fintype.card (Fin N))) :
    ¬ RootLinkBad
      ((tests i).badSet (rootFreePairObservation r M ell (tests i).time (tests i).root ω))
      ((tests i).time-(rootFreePairObservation r M ell (tests i).time (tests i).root ω).2.card)
      (rootSamplingPair r M ell (tests i).time ω) := by
  intro hbad
  apply hω.2.2.1 i
  refine ⟨hj,hK,hR,?_,hdegree,hdensity,hbad⟩
  exact hω.2.2.2 (tests i).root

/-- The common event has probability `1-o(1)`, uniformly over the admissible
terminal instance and every fixed registered family of root-free tests.
All three concrete test kinds fit this registry; the label count is proved,
not assumed. The threshold is chosen before the instance and registry. -/
theorem root_free_common_event_whp (r : ℕ) (hr : 3 ≤ r)
    (h hR : ℕ) (hh : 4*r ≤ h) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ B offset L cRoot : ℝ, 0 ≤ B → 0 ≤ offset → 0 < L → 0 < cRoot →
      ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ,
      ∀ N : ℕ, N₀ ≤ N → ∀ M : ℕ, ∀ ell : Fin N → ℕ,
      ∀ original : Finset (Finset (Fin N)),
      ∀ admissible : CoreAdmissible r M ell original offset,
      ∀ tests : RootTestIndex r original → RegisteredRootTest (Fin N) r hR,
      letI : Nonempty (TerminalState (Fin N) r M ell) := admissible.feasible
      1-ε ≤ (extensionLaw r M ell).event (RootFreeCommonEvent tests h c C L B cRoot) := by
  obtain ⟨c,C,hc,hC,hreg⟩ := common_regularity_whp r hr h
  refine ⟨c,C,hc,hC,?_⟩
  intro B offset L cRoot hB hoff hL hcRoot ε hε
  have hthird : 0 < ε/3 := by positivity
  obtain ⟨Nreg,hNreg⟩ := hreg offset L hoff hL.le (ε/3) hthird
  obtain ⟨Ncand,hNcand⟩ := uniform_common_candidate_whp r hr B offset c C L
    hB hoff hc hC hL h hh (ε/3) hthird
  obtain ⟨Nroot,hNroot⟩ := uniform_common_root_whp r hr cRoot hcRoot hR (ε/3) hthird
  obtain ⟨Ndef,hNdef⟩ := eventually_regular_root_deficit r C offset
  refine ⟨max (max Nreg Ncand) (max Nroot Ndef),?_⟩
  intro N hN M ell original admissible tests
  letI := admissible.feasible
  have hnreg : Nreg ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
  have hncand : Ncand ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
  have hnroot : Nroot ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hN
  have hndef : Ndef ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hN
  have hregular := hNreg (Fin N) (by simpa using hnreg) M ell original admissible
  have hcand := hNcand N hncand M ell original admissible
  have hroot := hNroot N hnroot M ell original tests
  rw [(extensionLaw r M ell).event_compl] at hcand hroot
  have hcand' : 1-ε/3 ≤ (extensionLaw r M ell).event
      (CommonCandidateBalance original h c C L B) := by linarith
  have hroot' : 1-ε/3 ≤ (extensionLaw r M ell).event
      (CommonRootTests tests M ell cRoot) := by linarith
  have hpair := event_inter_lower (extensionLaw r M ell)
    (CommonCandidateBalance original h c C L B) (CommonRootTests tests M ell cRoot)
    (ε/3) (ε/3) hcand' hroot'
  have hall := event_inter_lower (extensionLaw r M ell)
    (CommonRegularity r M ell original h c C L)
    (fun ω => CommonCandidateBalance original h c C L B ω ∧ CommonRootTests tests M ell cRoot ω)
    (ε/3) (ε/3+ε/3) hregular hpair
  have harith : ε/3+(ε/3+ε/3) = ε := by ring
  rw [harith] at hall
  apply hall.trans
  apply (extensionLaw r M ell).event_mono
  intro ω hω
  refine ⟨hω.1,hω.2.1,hω.2.2,?_⟩
  exact hNdef (Fin N) (by simpa using hndef) M ell original admissible ω.1 hω.1.1

end LooseHamilton
