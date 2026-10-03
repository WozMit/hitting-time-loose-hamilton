module

public import HittingTimeLooseHamilton.BootstrapCatalogueProbability
public import HittingTimeLooseHamilton.BootstrapFixedRegistry
public import HittingTimeLooseHamilton.RootFreeCommonEvent
public import HittingTimeLooseHamilton.RootSamplingInterpretation
public import HittingTimeLooseHamilton.TerminalFeasibilityScales

public section

/-! Ambient sampling gates for the actual fixed bootstrap catalogue. The root
sampling degree is measured before deletions and port filtering. -/
noncomputable section
namespace LooseHamilton.BootstrapCatalogue
open Finset Filter
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The fixed root-tail constant chosen from common lower regularity. -/
@[expose] def rootConstant (c : ℝ) : ℝ := c/2

theorem rootConstant_pos {c : ℝ} (hc : 0 < c) : 0 < rootConstant c := by
  unfold rootConstant; positivity

/-- The sampling population parameter is the actual ambient degree. -/
theorem sampling_degree_eq {r M j : ℕ} {ell : V → ℕ}
    (ω : TerminalState V r M ell × MissingOrder V r M)
    (hj : M ≤ j) (hK : j ≤ (completeEdges V r).card) (y : V) :
    j - (rootFreePairObservation r M ell j y ω).2.card =
      vertexDegree (extensionState ω.1 ω.2 j) y := by
  have hd := root_degree_from_rootfree y (extensionState ω.1 ω.2 j)
    (rootFreeEdges y (extensionState ω.1 ω.2 j)) rfl
  rw [extensionState_card _ _ _ hj hK] at hd
  exact hd.symm

omit [DecidableEq V] in
/-- Any eligible later time retains the terminal logarithmic mean bound. -/
theorem later_mean_lower {r M j : ℕ} (hj : M ≤ j)
    (hmean : Real.log (Fintype.card V : ℝ)/2 ≤ meanDegree (V := V) r M) :
    Real.log (Fintype.card V : ℝ)/2 ≤ meanDegree (V := V) r j := by
  apply hmean.trans
  unfold meanDegree
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hj) (Nat.cast_nonneg _))
    (Nat.cast_nonneg _)

/-- Common lower degree regularity implies the ambient logarithmic gate. -/
theorem sampling_degree_lower {r M j : ℕ} {ell : V → ℕ} {c C L : ℝ}
    (ω : TerminalState V r M ell × MissingOrder V r M)
    (hj : M ≤ j) (hK : j ≤ (completeEdges V r).card) (hc : 0 ≤ c)
    (hmean : Real.log (Fintype.card V : ℝ)/2 ≤ meanDegree (V := V) r M)
    (hreg : PathGraphRegular r c C L (extensionState ω.1 ω.2 j)) (y : V) :
    rootConstant c * FrameScales.L1 (Fintype.card V) ≤
      ((j - (rootFreePairObservation r M ell j y ω).2.card : ℕ) : ℝ) := by
  rw [sampling_degree_eq ω hj hK]
  have hh := mul_le_mul_of_nonneg_left (later_mean_lower hj hmean) hc
  have hd := hreg.lower_degree y
  rw [extensionState_card _ _ _ hj hK] at hd
  unfold rootConstant FrameScales.L1
  nlinarith

/-- The cutoff is independent of the matching, terminal state and offset. -/
theorem eventually_terminal_mean_lower :
    ∀ᶠ N : ℕ in atTop, ∀ (r M : ℕ) (ell : Fin N → ℕ)
      (original : Finset (Finset (Fin N))) (offset : ℝ),
      CoreAdmissible r M ell original offset →
      Real.log (N : ℝ)/2 ≤ meanDegree (V := Fin N) r M := by
  filter_upwards [eventually_feasibility_parameters 0] with N hN
  intro r M ell original offset hadm
  have hh := hN.2.1 (meanDegree (V := Fin N) r M)
    (by simpa using hadm.density_window)
  linarith [hN.1]

/-- No edge-presence condition remains for an actual catalogue entry. -/
theorem prescribed_present {r h M : ℕ} {ell : V → ℕ}
    {original : Finset (Finset V)} (hM : IsPairMatching original)
    (cP cE cPort : ℝ) (i : Index r original)
    (ω : TerminalState V r M ell × MissingOrder V r M) :
    (tests (h := h) hM cP cE cPort i).prescribed ⊆
      (rootSamplingPair r M ell i.2.val ω).2 := by
  rw [tests_prescribed]; exact empty_subset _

/-- The manuscript interval [M,K] is also the time interval for every
actual catalogue entry; base deletion does not alter this ambient time. -/
theorem tests_eligible_time {r h M : ℕ} {original : Finset (Finset V)}
    (hM : IsPairMatching original) (cP cE cPort : ℝ) (i : Index r original)
    (ht : M ≤ i.2.val ∧ i.2.val ≤ (completeEdges V r).card) :
    M ≤ (tests (h := h) hM cP cE cPort i).time ∧
      (tests (h := h) hM cP cE cPort i).time ≤ (completeEdges V r).card := by
  simpa only [tests_time] using ht

/-- Synthetic tag labels preserve the eligible ambient time exactly. -/
theorem fixedRegistry_eligible_time {r h M : ℕ} {original : Finset (Finset V)}
    (hM : IsPairMatching original) (hr : 3 ≤ r)
    (hroom : 2*original.card+2 ≤ Fintype.card V)
    (cP cE cPort : ℝ) (i : Index r original)
    (ht : M ≤ i.2.val ∧ i.2.val ≤ (completeEdges V r).card) :
    let T := fixedRegistry (h := h) hM hr hroom cP cE cPort
      (catalogueEmbedding hM hr hroom i)
    M ≤ T.time ∧ T.time ≤ (completeEdges V r).card := by
  dsimp only
  rw [fixedRegistry_entry]
  exact tests_eligible_time hM cP cE cPort i ht

end LooseHamilton.BootstrapCatalogue
