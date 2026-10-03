module

public import HittingTimeLooseHamilton.TerminalLowSetProbability
public import HittingTimeLooseHamilton.TerminalLowSetScales
public import HittingTimeLooseHamilton.TerminalFeasibility
public import HittingTimeLooseHamilton.TerminalLowSetDecay

public section

/-! Uniform terminal low-set probability bound for the manuscript's core setup. -/
noncomputable section
namespace LooseHamilton
open Filter

lemma terminal_low_set_core_eventually (r : ℕ) (hr : 3 ≤ r) (B : ℝ) (hB : 0 ≤ B) :
    ∀ᶠ n : ℕ in atTop, ∀ (V : Type) [Fintype V] [DecidableEq V], Fintype.card V=n →
      ∀ (M : ℕ) (ell : V → ℕ) (markers : Finset (Finset V)),
        (hadm : CoreAdmissible r M ell markers B) →
        letI := hadm.feasible
        (terminalLaw r M ell).event (fun F =>
          (n:ℝ)^(1/4:ℝ) < ((terminalLowVertices F.val).card:ℝ)) ≤
          (((n.choose (terminalLowSetSize n):ℝ)*
            Real.exp (-(82/100:ℝ)*terminalLowSetSize n*Real.log (n:ℝ)) +
              Real.exp (-(M:ℝ)/1010000)) * Real.exp ((n:ℝ)^(1/10:ℝ))) := by
  obtain ⟨N₀,hN₀⟩ := terminal_feasibility_core r hr B hB
  filter_upwards [eventually_ge_atTop N₀,eventually_ge_atTop r,
    terminalLowSet_mean_eventually (show 1≤r by omega)] with n hn hrn hmean
  intro V _ _ hV M ell markers hadm
  letI := hadm.feasible
  let K := Fintype.card (Edge V r)
  let p : ℝ := (99/100:ℝ)*M/K
  have hK : K=n.choose r := by simp [K,completeEdges_card,hV]
  have hK0 : (0:ℝ)<K := by rw [hK]; exact_mod_cast Nat.choose_pos hrn
  have hM : (M:ℝ)≤K := by
    obtain ⟨F⟩ := hadm.feasible
    exact_mod_cast (show M≤K by simpa [K] using terminal_size_le F)
  have hp0 : 0≤p := by dsimp [p]; positivity
  have hp1 : p≤1 := by
    apply (div_le_iff₀ hK0).mpr
    nlinarith [show (0:ℝ)≤M from Nat.cast_nonneg M]
  have hsize : p*Fintype.card (Edge V r)=(99/100:ℝ)*M := by
    change p*K=_
    dsimp [p]
    field_simp <;> ring
  have hd : |(r:ℝ)*M/n-Real.log n|≤3*Real.log (Real.log n) := by
    simpa [meanDegree,hV] using hadm.density_window
  have hm : (98/100:ℝ)*Real.log (Fintype.card V:ℝ) ≤
      p*((Fintype.card V-terminalLowSetTestSize (Fintype.card V)).choose (r-1):ℝ) := by
    simpa [p,hK,hV,terminalLowSetTestSize,terminalLowSetSize] using hmean M hd
  have hb := hN₀ V (by omega) M ell markers hadm
  simpa [hV,terminalLowSetTestSize,terminalLowSetSize] using
    terminal_low_set_probability_finite r M ell (by omega) (by omega) p hp0 hp1 hsize hm hb

lemma terminal_low_set_tail_eventually (r : ℕ) (hr : 3 ≤ r) (B : ℝ) (hB : 0 ≤ B) :
    ∀ᶠ n : ℕ in atTop, ∀ (V : Type) [Fintype V] [DecidableEq V], Fintype.card V=n →
      ∀ (M : ℕ) (ell : V → ℕ) (markers : Finset (Finset V)),
        (hadm : CoreAdmissible r M ell markers B) →
        letI := hadm.feasible
        (terminalLaw r M ell).event (fun F =>
          (n:ℝ)^(1/4:ℝ) < ((terminalLowVertices F.val).card:ℝ)) ≤ terminalLowSetError n := by
  filter_upwards [terminal_low_set_core_eventually r hr B hB,
    terminalLowSet_conditioned_bound_eventually (show 1≤r by omega)] with n hc hs
  intro V _ _ hV M ell markers hadm
  letI := hadm.feasible
  apply (hc V hV M ell markers hadm).trans
  have hd : |(r:ℝ)*M/n-Real.log n|≤3*Real.log (Real.log n) := by
    simpa [meanDegree,hV] using hadm.density_window
  simpa only [mul_comm] using hs M hd
end LooseHamilton
