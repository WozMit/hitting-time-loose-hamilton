module

public import HittingTimeLooseHamilton.BootstrapAllEdgeMarginals
public import HittingTimeLooseHamilton.BootstrapOrdinaryMaximum
public import HittingTimeLooseHamilton.BootstrapPortMaximum

public section

/-! Uniform all-edge marginals on the single fixed common event. In particular,
the logarithmic eligibility condition does not silently assert a positive cycle
count: the zero-count case is included by the finite marginal theorem. -/
noncomputable section
namespace LooseHamilton.BootstrapAllEdgeMaximum
open Finset Filter BootstrapCatalogue BootstrapConstants

/-- Coefficient of the inverse ambient mean in the all-edge bound. -/
@[expose] def constant (r : ℕ) (c : ℝ) : ℝ :=
  (r.choose 2 : ℝ) * max (BootstrapOrdinaryMaximum.constant r c)
    (BootstrapPortCap.constant r c)

theorem constant_nonneg (r : ℕ) (c : ℝ) : 0 ≤ constant r c := by
  apply mul_nonneg (Nat.cast_nonneg _)
  exact le_trans (Nat.cast_nonneg r) (le_trans (le_max_left _ _) (le_max_left _ _))

/-- All true-edge marginals, simultaneously at every eligible later time, for
all uniformities at least three. The registry and constants precede the outcome,
and all auxiliary density and mobility hypotheses have been discharged. -/
theorem eventually_all_edge_marginals (r : ℕ) (hr : 3 ≤ r) (c C : ℝ)
    (hc : 0 < c) (hC : 0 ≤ C) :
    ∀ᶠ N : ℕ in atTop, ∀ (m : ℕ) (ell : Fin N → ℕ)
      (M : Finset (Finset (Fin N))) (offset : ℝ)
      (hadm : CoreAdmissible r m ell M offset),
      ∃ hroom : 2*M.card+2 ≤ Fintype.card (Fin N),
      ∀ (h hR : ℕ) (L : ℝ)
        (ω : CandidateBalance.Outcome (Fin N) r m ell),
      RootFreeCommonEvent
        (fixedRegistry (h:=hR) hadm.marker_matching hr hroom
          (rootThreshold r) (rootThreshold r) (portThreshold r c))
        h c C L 2 (rootConstant c) ω →
      ∀ j : ℕ, m ≤ j → j ≤ (completeEdges (Fin N) r).card →
      let H := extensionState ω.1 ω.2 j
      let X := cycleCount r M H (originalPorts M)
      logarithmicBaseline r (ordinaryEdgeCount r M) j M -
        (N:ℝ)/Real.sqrt (Real.log N) ≤ Real.log (X:ℝ) →
      ∀ e : Finset (Fin N),
      cycleMarginal r M H (originalPorts M) e ≤
        constant r c / meanDegree (V:=Fin N) r j := by
  classical
  filter_upwards [BootstrapOrdinaryMaximum.eventually_completion_maximum r hr c C hc hC,
    BootstrapPortMaximum.eventually_port_maximum r hr c hc,
    eventually_terminal_mean_lower, eventually_gt_atTop (max 1 (5*(r-1)))]
    with N hord hport hmean hN
  intro m ell M offset hadm
  obtain ⟨hroom,hord⟩ := hord m ell M offset hadm
  obtain ⟨hroom',hport⟩ := hport m ell M offset hadm
  refine ⟨hroom,?_⟩
  intro h hR L ω hω j hj hK H X hAX e
  have hmean' : Real.log (Fintype.card (Fin N):ℝ)/2 ≤ meanDegree (V:=Fin N) r m := by
    simpa using hmean r m ell M offset hadm
  have hmu : 0 < meanDegree (V:=Fin N) r j := by
    have hh := later_mean_lower hj hmean'
    have hp : 0 < Real.log (Fintype.card (Fin N):ℝ) := by
      apply Real.log_pos
      simp only [Fintype.card_fin]
      exact_mod_cast (show 1<N by omega)
    linarith
  have hH : H ⊆ completeEdges (Fin N) r := extensionState_subset ω.1 ω.2 j
  have hf : fixedPortHost H (originalPorts M) = H ∩ allowedEdges r (originalPorts M) := by
    ext a
    simp only [fixedPortHost,mem_filter,mem_inter,mem_allowedEdges]
    constructor
    · rintro ⟨ha,hp⟩; exact ⟨ha,(mem_completeEdges _ _).mp (hH ha),hp⟩
    · rintro ⟨ha,_,hp⟩; exact ⟨ha,hp⟩
  apply BootstrapAllEdgeMarginals.all_edges_le hr hadm.marker_matching
    (by simpa only [Fintype.card_fin] using (show 5*(r-1)<N by omega))
    (BootstrapOrdinaryMaximum.constant r c) (BootstrapPortCap.constant r c)
    (meanDegree (V:=Fin N) r j)
    (le_trans (Nat.cast_nonneg r) (le_max_left _ _))
    (BootstrapPortCap.constant_pos hr c).le hmu
    (fun hX P y z hs => hord h hR (portThreshold r c) L ω hω j hj hK hX hAX P y z hs)
    ?_ e
  intro hX P y z u hs hy hm hyz
  have hb := hport h hR C L ω hω j hj hK hX hAX P y z u hs hy hm hyz
  change (rootFreePortSource r M (fixedPortHost H (originalPorts M)) y z P u:ℝ) ≤ _ at hb
  rw [hf] at hb
  exact hb

end LooseHamilton.BootstrapAllEdgeMaximum
