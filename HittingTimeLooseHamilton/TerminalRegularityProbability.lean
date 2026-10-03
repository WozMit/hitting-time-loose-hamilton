module

public import HittingTimeLooseHamilton.TerminalRegularityStatement
public import HittingTimeLooseHamilton.TerminalRegularityReduction
public import HittingTimeLooseHamilton.OneVertexMaximumDegree
public import HittingTimeLooseHamilton.TerminalAssociationControl
public import HittingTimeLooseHamilton.TerminalLowSet

public section

/-! Uniform high probability of all four terminal regularity conditions. -/
noncomputable section
namespace LooseHamilton
open Filter

/-- A single permitted logarithmic maximum-degree constant. -/
@[expose] def terminalRegularityConstant : ℝ := poissonMaximumConstant 2

lemma terminalRegularityConstant_pos : 0 < terminalRegularityConstant := by
  unfold terminalRegularityConstant poissonMaximumConstant
  positivity

/-- Explicit vanishing error, independent of M, offsets and the marked matching. -/
@[expose] def terminalRegularityError (r n : ℕ) : ℝ :=
  (n:ℝ)^(-2:ℝ) + terminalLowSetError n +
    terminalPairError r n terminalRegularityConstant +
    terminalStarError r n terminalRegularityConstant

lemma terminalRegularityError_tendsto (r : ℕ) :
    Tendsto (terminalRegularityError r) atTop (nhds 0) := by
  have hp : Tendsto (fun n : ℕ => (n:ℝ)^(-2:ℝ)) atTop (nhds 0) :=
    (tendsto_rpow_neg_atTop (by norm_num : (0:ℝ)<2)).comp tendsto_natCast_atTop_atTop
  obtain ⟨hpair,hstar⟩ := terminal_association_error_limits r terminalRegularityConstant
  have h := ((hp.add terminalLowSetError_tendsto).add hpair).add hstar
  simp only [add_zero] at h
  exact h

/-- All probability ingredients are established by the previously compiled bounds. -/
theorem terminal_regular_failure_eventually (r : ℕ) (hr : 3 ≤ r) (B : ℝ) (hB : 0 ≤ B) :
    ∀ᶠ n : ℕ in atTop, ∀ (V : Type) [Fintype V] [DecidableEq V],
      Fintype.card V = n → ∀ (M : ℕ) (ell : V → ℕ) (markers : Finset (Finset V)),
      ∀ hadm : CoreAdmissible r M ell markers B,
      letI : Nonempty (TerminalState V r M ell) := hadm.feasible
      1-(terminalLaw r M ell).event (fun F => TerminalRegular terminalRegularityConstant F.val) ≤
        terminalRegularityError r n := by
  filter_upwards [core_maximum_degree_tail_eventually 2 B,
    terminal_low_set_tail_eventually r hr B hB,
    terminal_association_control_eventually r hr terminalRegularityConstant_pos.le]
      with n hmax hlow hassoc
  intro V _ _ hcard M ell markers hadm
  letI : Nonempty (TerminalState V r M ell) := hadm.feasible
  have hm := hmax V hcard r M ell markers hadm
  have hl := hlow V hcard M ell markers hadm
  obtain ⟨hp,hs⟩ := hassoc V hcard M ell (by simpa [hcard] using hadm.density_window)
  have hsum := terminal_regular_failure_le (terminalLaw r M ell)
    (fun F => F.val) terminalRegularityConstant
  have hm' : (terminalLaw r M ell).event (fun F => ∃ v,
      terminalRegularityConstant*Real.log (Fintype.card V:ℝ) < (vertexDegree F.val v:ℝ)) ≤
        (n:ℝ)^(-2:ℝ) := by convert hm using 1 <;> simp only [terminalRegularityConstant,hcard]
  have hl' : (terminalLaw r M ell).event (fun F =>
      (Fintype.card V:ℝ)^(1/4:ℝ) < ((terminalLowVertices F.val).card:ℝ)) ≤ terminalLowSetError n := by
    simpa only [hcard] using hl
  exact hsum.trans (add_le_add (add_le_add (add_le_add hm' hl') hp) hs)

/-- The uniform eta-cutoff form of probability tending to one. -/
theorem terminal_regularity_whp (r : ℕ) (hr : 3 ≤ r) (B : ℝ) (hB : 0 ≤ B) :
    TerminalRegularityWhp r terminalRegularityConstant B := by
  intro η hη
  have he := (tendsto_order.mp (terminalRegularityError_tendsto r)).2 η hη
  obtain ⟨N₀,hN₀⟩ := eventually_atTop.mp
    ((terminal_regular_failure_eventually r hr B hB).and he)
  refine ⟨N₀,?_⟩
  intro V _ _ hn M ell markers hadm
  letI : Nonempty (TerminalState V r M ell) := hadm.feasible
  obtain ⟨hb,he⟩ := hN₀ (Fintype.card V) hn
  have hp := hb V rfl M ell markers hadm
  linarith
end LooseHamilton
