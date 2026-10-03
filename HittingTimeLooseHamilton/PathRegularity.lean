module

public import HittingTimeLooseHamilton.PathRegularityStatement
public import HittingTimeLooseHamilton.PathRegularityProbability
public import HittingTimeLooseHamilton.PathPerturbationAsymptotic

public section

/-! Proposition 4.4: path regularity and the stated perturbation variants. -/
noncomputable section
namespace LooseHamilton
open Filter

/-- All displayed bounds hold uniformly along the actual Q path, together
with bounded induced deletions and the fixed original-port prohibition. -/
theorem proposition44 : Proposition44 := by
  intro r hr
  let c := pathDegreeLowerFactor r
  let C := pathRegularityConstant r
  have hc : 0<c := pathDegreeLowerFactor_pos r
  have hC : 0<C := pathRegularityConstant_pos r
  refine ⟨c,C,hc,hC,?_⟩
  intro h
  refine ⟨c/4,32*C,by positivity,by positivity,?_⟩
  intro B L hB hL η hη
  have he := (tendsto_order.mp (pathRegularityError_tendsto hr)).2 η hη
  obtain ⟨N₀,hN₀⟩ := eventually_atTop.mp
    (((path_regular_failure_eventually r hr B (L+1) hB (by linarith)).and
      (eventually_path_regular_perturbations r h c C L (by omega) hc hC.le hL)).and he)
  refine ⟨N₀,?_⟩
  intro V _ _ hn M ell markers hadm
  letI : Nonempty (TerminalState V r M ell) := hadm.feasible
  obtain ⟨⟨hprob,hpert⟩,herr⟩ := hN₀ (Fintype.card V) hn
  have hp := hprob V rfl M ell markers hadm
  have hports : ((originalPorts markers).card:ℝ) ≤
      2*(Fintype.card V:ℝ)^(1/10:ℝ) := by
    rw [hadm.marker_matching.ports_card,Nat.cast_mul,Nat.cast_ofNat]
    exact mul_le_mul_of_nonneg_left hadm.markers_small (by norm_num)
  have hgood : 1-η ≤ (extensionLaw r M ell).event (PathRegularityEvent r M ell c C (L+1)) := by
    change 1-(extensionLaw r M ell).event (PathRegularityEvent r M ell c C (L+1)) ≤ _ at hp
    linarith
  apply hgood.trans
  apply FiniteEntropy.Law.event_mono
  intro ω hω
  refine ⟨?_,?_,?_⟩
  · intro j hj hjK
    exact (hω j hj hjK).mono le_rfl le_rfl (by linarith)
  · intro j hj hjK Z hZ
    have ht := (hpert V rfl (extensionState ω.1 ω.2 j) (hω j hj hjK)
      (originalPorts markers) hports Z hZ).1
    exact ht.mono le_rfl (by linarith) le_rfl
  · intro j hj hjK Z hZ
    exact (hpert V rfl (extensionState ω.1 ω.2 j) (hω j hj hjK)
      (originalPorts markers) hports Z hZ).2
end LooseHamilton
