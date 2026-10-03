module

public import HittingTimeLooseHamilton.CoreCountStatement
public import HittingTimeLooseHamilton.FirstFailureEvents
public import HittingTimeLooseHamilton.ExtensionTerminalMarginal

public section

/-! Finite transfer from the path baseline bound to the terminal benchmark. -/
noncomputable section
namespace LooseHamilton.CoreCount
variable {N r m : ℕ}

theorem good_of_no_pathFailure (markers : Finset (Finset (Fin N)))
    (D B : ℝ) (H : ℕ → SimpleHypergraph (Fin N))
    (hm : m ≤ (completeEdges (Fin N) r).card)
    (hbench : |logarithmicBaseline r (ordinaryEdgeCount r markers) m markers -
      logarithmicBenchmark r N (ordinaryEdgeCount r markers) m| ≤ (N:ℝ)/Real.log N)
    (h : ¬ FirstFailure.PathFailure r m markers D (B*N/Real.log N) H) :
    Good r m markers (B+1) (H m) := by
  obtain ⟨hpos,hlo,_⟩ := (FirstFailure.not_pathFailure_iff r m markers D
    (B*N/Real.log N) H).mp h m le_rfl hm
  refine ⟨hpos,?_⟩
  have he := (abs_le.mp hbench).1
  have hc : (B+1)*N/Real.log N = B*N/Real.log N + (N:ℝ)/Real.log N := by ring
  rw [hc]
  linarith

theorem terminal_probability_bound (markers : Finset (Finset (Fin N)))
    (ell : Fin N → ℕ) [Nonempty (TerminalState (Fin N) r m ell)]
    (D B ε : ℝ)
    (hbench : |logarithmicBaseline r (ordinaryEdgeCount r markers) m markers -
      logarithmicBenchmark r N (ordinaryEdgeCount r markers) m| ≤ (N:ℝ)/Real.log N)
    (hprob : (extensionLaw r m ell).event (fun ω =>
      FirstFailure.PathFailure r m markers D (B*N/Real.log N)
        (extensionState ω.1 ω.2)) ≤ ε) :
    1-ε ≤ (terminalLaw r m ell).event (fun F => Good r m markers (B+1) F.val) := by
  have hm := terminal_size_le (Classical.choice ‹Nonempty (TerminalState (Fin N) r m ell)›)
  rw [← extension_terminal_event r m ell (Good r m markers (B+1))]
  calc
    1-ε ≤ (extensionLaw r m ell).event (fun ω =>
        ¬ FirstFailure.PathFailure r m markers D (B*N/Real.log N)
          (extensionState ω.1 ω.2)) := by
      rw [FiniteEntropy.Law.event_compl]
      linarith
    _ ≤ _ := (extensionLaw r m ell).event_mono (by
      intro ω hω
      simpa only [extensionState_initial] using
        good_of_no_pathFailure markers D B (extensionState ω.1 ω.2) hm hbench hω)

end LooseHamilton.CoreCount
