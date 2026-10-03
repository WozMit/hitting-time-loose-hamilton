module

public import HittingTimeLooseHamilton.HittingTimeCoreRelabel
public import HittingTimeLooseHamilton.HittingTimeTerminalRelabel
public import HittingTimeLooseHamilton.CoreCount

public section

noncomputable section
namespace LooseHamilton.HittingTimeCore

/-- The core count theorem supplies an actual allowed mixed cycle, uniformly
on every finite vertex type. Relabelling preserves the genuine terminal law. -/
theorem terminal_zero_count_probability (r : ℕ) (hr : 3 ≤ r)
    (offset : ℝ) (hoff : 0 ≤ offset) (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ (V : Type*) [Fintype V] [DecidableEq V], N₀ ≤ Fintype.card V →
      ∀ (m : ℕ) (ell : V → ℕ) (markers : Finset (Finset V)),
      ∀ hadm : CoreAdmissible r m ell markers offset,
      letI : Nonempty (TerminalState V r m ell) := hadm.feasible
      (terminalLaw r m ell).event (fun F =>
        ¬ 0 < cycleCount r markers F.val (originalPorts markers)) ≤ ε := by
  obtain ⟨C,_hC,hcore⟩ := CoreCount.conditioned_core_count r hr
  obtain ⟨N₀,hN₀⟩ := hcore offset hoff ε hε
  refine ⟨N₀,?_⟩
  intro V _ _ hN m ell markers hadm
  letI : Nonempty (TerminalState V r m ell) := hadm.feasible
  let σ := Fintype.equivFin V
  have hadm' := admissible_relabel σ hadm
  letI : Nonempty (TerminalState (Fin (Fintype.card V)) r m (fun w => ell (σ.symm w))) :=
    hadm'.feasible
  have hp := hN₀ (Fintype.card V) hN m (fun w => ell (σ.symm w)) (vertexEdges σ markers) hadm'
  have hbad : (terminalLaw r m (fun w => ell (σ.symm w))).event (fun F =>
      ¬ 0 < cycleCount r (vertexEdges σ markers) F.val (originalPorts (vertexEdges σ markers))) ≤ ε := by
    calc
      _ ≤ (terminalLaw r m (fun w => ell (σ.symm w))).event (fun F =>
          ¬ CoreCount.Good r m (vertexEdges σ markers) C F.val) :=
        (terminalLaw r m (fun w => ell (σ.symm w))).event_mono
          (fun _ hbad hgood => hbad hgood.1)
      _ ≤ ε := by rw [FiniteEntropy.Law.event_compl]; linarith
  have he := terminal_event_relabel σ r m ell (fun F =>
    ¬ 0 < cycleCount r (vertexEdges σ markers) F.val (originalPorts (vertexEdges σ markers)))
  rw [← he] at hbad
  simpa only [terminalEquiv_val,cycleCount_pos_vertexEdges_iff] using hbad

/-- Explicit existential version: failure means that no spanning connected
mixed cycle through the prescribed markers uses only the original allowed edges. -/
theorem terminal_no_cycle_probability (r : ℕ) (hr : 3 ≤ r)
    (offset : ℝ) (hoff : 0 ≤ offset) (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ (V : Type*) [Fintype V] [DecidableEq V], N₀ ≤ Fintype.card V →
      ∀ (m : ℕ) (ell : V → ℕ) (markers : Finset (Finset V)),
      ∀ hadm : CoreAdmissible r m ell markers offset,
      letI : Nonempty (TerminalState V r m ell) := hadm.feasible
      (terminalLaw r m ell).event (fun F => ¬ ∃ edges : SimpleHypergraph V,
        IsMixedCycle r markers edges ∧ edges ⊆ F.val ∧
          edges ⊆ allowedEdges r (originalPorts markers)) ≤ ε := by
  obtain ⟨N₀,hN₀⟩ := terminal_zero_count_probability r hr offset hoff ε hε
  refine ⟨N₀,?_⟩
  intro V _ _ hN m ell markers hadm
  letI : Nonempty (TerminalState V r m ell) := hadm.feasible
  simpa only [cycleCount_pos_iff] using hN₀ V hN m ell markers hadm
end LooseHamilton.HittingTimeCore
