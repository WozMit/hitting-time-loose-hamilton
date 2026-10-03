module

public import HittingTimeLooseHamilton.BootstrapPortCap
public import HittingTimeLooseHamilton.BootstrapPortCommonDensity

public section

/-! Uniform cap on every genuine original-port contraction. The final theorem
has no density, root nonfailure, or large-source hypothesis. -/
noncomputable section
namespace LooseHamilton.BootstrapPortMaximum
open Finset Filter BootstrapCatalogue BootstrapConstants

/-- Actual original-port sources have a uniform inverse-raw-mean cap on the
fixed common event. Small sources are included, for every uniformity `r≥3`. -/
theorem eventually_port_maximum (r : ℕ) (hr : 3 ≤ r) (c : ℝ) (hc : 0<c) :
    ∀ᶠ N : ℕ in atTop, ∀ (m : ℕ) (ell : Fin N → ℕ)
      (M : Finset (Finset (Fin N))) (offset : ℝ)
      (hadm : CoreAdmissible r m ell M offset),
      ∃ hroom : 2*M.card+2 ≤ Fintype.card (Fin N),
      ∀ (h hR : ℕ) (C L : ℝ)
        (ω : CandidateBalance.Outcome (Fin N) r m ell),
      RootFreeCommonEvent
        (fixedRegistry (h:=hR) hadm.marker_matching hr hroom
          (rootThreshold r) (rootThreshold r) (portThreshold r c))
        h c C L 2 (rootConstant c) ω →
      ∀ j : ℕ, m ≤ j → j ≤ (completeEdges (Fin N) r).card →
      let H := extensionState ω.1 ω.2 j
      let X := cycleCount r M H (originalPorts M)
      0 < X → logarithmicBaseline r (ordinaryEdgeCount r M) j M -
        (N:ℝ)/Real.sqrt (Real.log N) ≤ Real.log (X:ℝ) →
      ∀ (P : Finset (Fin N)) (y z u : Fin N),
      LegalPrivateCompletion r (M.erase {y,z}) P {u,z} →
      y ∉ P ∪ {u,z} → {y,z} ∈ M → y ≠ z →
      (rootFreePortSource r M (fixedPortHost H (originalPorts M)) y z P u:ℝ) ≤
        BootstrapPortCap.constant r c*(X:ℝ)/meanDegree (V:=Fin N) r j := by
  filter_upwards [BootstrapPortCommonDensity.eventually_port_density r hr c hc,
    eventually_terminal_mean_lower, eventually_gt_atTop (max 1 (5*(r-1)))]
    with N hden hmean hN
  intro m ell M offset hadm
  obtain ⟨hroom,hden⟩ := hden m ell M offset hadm
  refine ⟨hroom,?_⟩
  intro h hR C L ω hω j hj hK H X hX hAX P y z u hs hy hm hyz
  have hmean' : Real.log (Fintype.card (Fin N):ℝ)/2 ≤ meanDegree (V:=Fin N) r m := by
    simpa using hmean r m ell M offset hadm
  have hcard : H.card=j := extensionState_card ω.1 ω.2 j hj hK
  have hmu : 0 < meanDegree (V:=Fin N) r H.card := by
    rw [hcard]
    have hh := later_mean_lower hj hmean'
    have hp : 0 < Real.log (Fintype.card (Fin N):ℝ) := by
      apply Real.log_pos
      simp only [Fintype.card_fin]
      exact_mod_cast (show 1<N by omega)
    linarith
  let j' : Fin ((Fintype.card (Fin N))^r+1) := ⟨j,by
    have hh : j ≤ N^r := hK.trans (by
      simpa only [completeEdges_card,Fintype.card_fin] using Nat.choose_le_pow N r)
    simp only [Fintype.card_fin]
    omega⟩
  have hb := BootstrapPortCap.source_cap_including_tiny hr (by omega : 1≤N)
    M ω.1.val H hadm.marker_matching (extensionState_subset ω.1 ω.2 j)
    (by omega) hR j c hc hmu P y z u hyz hm ((hω.1.2.1 j hj hK).lower_degree y)
  apply (show (rootFreePortSource r M (fixedPortHost H (originalPorts M)) y z P u:ℝ) ≤
    BootstrapPortCap.constant r c*(X:ℝ)/meanDegree (V:=Fin N) r H.card from ?_).trans_eq
    (by rw [hcard])
  apply hb
  intro hlarge
  exact BootstrapPortCap.nonfailure hadm.marker_matching hr hroom
    (rootThreshold r) (rootThreshold r) (portThreshold r c) c C L hc.le ω hω hmean'
    P hs.private_card y z u hs hy hyz j' hj hK
    (hden h hR C L ω hω j hj hK hX hAX P y z u hs hy hm hyz hlarge).le

end LooseHamilton.BootstrapPortMaximum
