module

public import HittingTimeLooseHamilton.FirstFailureStatement
public import HittingTimeLooseHamilton.FirstFailurePathLaw
public import HittingTimeLooseHamilton.FirstFailureCycleBaseline
public import HittingTimeLooseHamilton.FirstFailureProbability

public section

noncomputable section
namespace LooseHamilton.FirstFailure
open Finset
variable {N r m : ℕ}

@[expose] def CapPathFailure (markers : Finset (Finset (Fin N))) (D T : ℝ)
    (H : ℕ → SimpleHypergraph (Fin N)) : Prop :=
  ∃ j, m ≤ j ∧ j ≤ (completeEdges (Fin N) r).card ∧
    logarithmicBaseline r (ordinaryEdgeCount r markers) j markers - T ≤
      Real.log (cycleCount r markers (H j) (originalPorts markers) : ℝ) ∧
    ∃ e ∈ H j, D*(ordinaryEdgeCount r markers : ℝ)/j <
      cycleMarginal r markers (H j) (originalPorts markers) e

lemma marginal_violation_iff (markers : Finset (Finset (Fin N)))
    (H : Finset (Edge (Fin N) r)) (b : ℝ) :
    (∃ e ∈ H, b < StoppedCounting.marginal (family r markers (originalPorts markers)) H e) ↔
      ∃ e ∈ host H, b < cycleMarginal r markers (host H) (originalPorts markers) e := by
  simp only [marginal_eq]
  constructor
  · rintro ⟨e,he,hq⟩
    exact ⟨e.val,(mem_host H e).mpr he,hq⟩
  · rintro ⟨e,he,hq⟩
    obtain ⟨f,hf,rfl⟩ := mem_image.mp he
    exact ⟨f,hf,hq⟩

lemma rank_path_failure_iff (markers : Finset (Finset (Fin N))) (D B : ℝ)
    (ρ : FiniteOrder (Edge (Fin N) r)) (hm : m ≤ (completeEdges (Fin N) r).card) :
    PathFailure r m markers D B (fun j => host (orderPrefix ρ (max m j))) ↔
      StoppedCounting.PathFailure (family r markers (originalPorts markers)) D
        (ordinaryEdgeCount r markers) m B ρ := by
  simp only [PathFailure,StoppedCounting.PathFailure,StoppedCounting.state,
    familyCount_eq,baseline_eq,Fintype.card_coe,marginal_violation_iff]
  constructor
  · rintro ⟨j,hjm,hjK,hf⟩
    refine ⟨(completeEdges (Fin N) r).card-j,by omega,?_⟩
    have hj : (completeEdges (Fin N) r).card-((completeEdges (Fin N) r).card-j)=j := by omega
    simpa only [hj,max_eq_right hjm] using hf
  · rintro ⟨t,ht,hf⟩
    refine ⟨(completeEdges (Fin N) r).card-t,by omega,Nat.sub_le _ _,?_⟩
    have hj : m ≤ (completeEdges (Fin N) r).card-t := by omega
    simpa only [max_eq_right hj] using hf

lemma rank_cap_failure_iff (markers : Finset (Finset (Fin N))) (D T : ℝ)
    (ρ : FiniteOrder (Edge (Fin N) r)) (hm : m ≤ (completeEdges (Fin N) r).card) :
    CapPathFailure (r:=r) (m:=m) markers D T (fun j => host (orderPrefix ρ (max m j))) ↔
      StoppedCounting.CapFailure (family r markers (originalPorts markers)) D
        (ordinaryEdgeCount r markers) m T ρ := by
  simp only [CapPathFailure,StoppedCounting.CapFailure,StoppedCounting.state,
    familyCount_eq,baseline_eq,Fintype.card_coe,marginal_violation_iff]
  constructor
  · rintro ⟨j,hjm,hjK,hf⟩
    refine ⟨(completeEdges (Fin N) r).card-j,by omega,?_⟩
    have hj : (completeEdges (Fin N) r).card-((completeEdges (Fin N) r).card-j)=j := by omega
    simpa only [hj,max_eq_right hjm] using hf
  · rintro ⟨t,ht,hf⟩
    refine ⟨(completeEdges (Fin N) r).card-t,by omega,Nat.sub_le _ _,?_⟩
    have hj : m ≤ (completeEdges (Fin N) r).card-t := by omega
    simpa only [max_eq_right hj] using hf

/-- A finite first-failure estimate under the original extension law, prior to
any asymptotic choice of the count and variance budgets. -/
theorem finite_probability_bound (markers : Finset (Finset (Fin N)))
    (ell : Fin N → ℕ) [Nonempty (TerminalState (Fin N) r m ell)]
    (D a B W : ℝ) (hr : 3 ≤ r)
    (hfull : 0 < cycleCount r markers (completeEdges (Fin N) r) (originalPorts markers))
    (hm : 0 < m) (hD : 1 ≤ D)
    (hsmall : D*(ordinaryEdgeCount r markers : ℝ)/m ≤ (1/2:ℝ))
    (ha : 0 < a) (hW : 0 < W)
    (hVW : StoppedCounting.variance D (ordinaryEdgeCount r markers) m
      (completeEdges (Fin N) r).card ≤ W)
    (hbudget : a+W ≤ B) (hmargin : a+W < (N:ℝ)/Real.sqrt (Real.log N)) :
    (extensionLaw r m ell).event (fun ω => PathFailure r m markers D B (extensionState ω.1 ω.2)) ≤
      (extensionLaw r m ell).event (UniformMarginalCap.Failure markers D) +
        (terminalFeasibilityProbability r m ell)⁻¹ * Real.exp (-a^2/(2*W)) := by
  have hmK : m ≤ (completeEdges (Fin N) r).card :=
    terminal_size_le (Classical.choice ‹Nonempty (TerminalState (Fin N) r m ell)›)
  have hp := StoppedCounting.first_failure_probability_budget
    (family r markers (originalPorts markers)) (ordinaryEdgeCount r markers) m D a B
    ((N:ℝ)/Real.sqrt (Real.log N)) W (full_family_nonempty r markers _ hfull)
    (uniformFamily markers _ hr) hm (by simpa using hmK) hD hsmall ha hW
    (by simpa using hVW) hbudget hmargin (FirstFailurePathLaw.terminalDegree ell)
    (FirstFailurePathLaw.terminal_event_pos (r:=r) m ell)
  have hpath := FirstFailurePathLaw.extension_event_eq_conditioned_deletion (r:=r) m ell
    (PathFailure r m markers D B)
  have hcap := FirstFailurePathLaw.extension_event_eq_conditioned_deletion (r:=r) m ell
    (CapPathFailure (r:=r) (m:=m) markers D ((N:ℝ)/Real.sqrt (Real.log N)))
  have hepath : (fun ρ : FiniteOrder (Edge (Fin N) r) =>
      PathFailure r m markers D B (fun j => FirstFailurePathLaw.host (orderPrefix ρ (max m j)))) =
      StoppedCounting.PathFailure (family r markers (originalPorts markers)) D
        (ordinaryEdgeCount r markers) m B := by
    funext ρ
    exact propext (rank_path_failure_iff markers D B ρ hmK)
  have hecap : (fun ρ : FiniteOrder (Edge (Fin N) r) =>
      CapPathFailure (r:=r) (m:=m) markers D ((N:ℝ)/Real.sqrt (Real.log N))
        (fun j => FirstFailurePathLaw.host (orderPrefix ρ (max m j)))) =
      StoppedCounting.CapFailure (family r markers (originalPorts markers)) D
        (ordinaryEdgeCount r markers) m ((N:ℝ)/Real.sqrt (Real.log N)) := by
    funext ρ
    exact propext (rank_cap_failure_iff markers D _ ρ hmK)
  rw [hepath] at hpath
  rw [hecap] at hcap
  rw [← hpath,← hcap,FirstFailurePathLaw.terminal_event_eq_beta] at hp
  exact hp

end LooseHamilton.FirstFailure
