module

public import HittingTimeLooseHamilton.BootstrapPortFiniteDensity
public import HittingTimeLooseHamilton.BootstrapPortDensityScales

public section

/-! The quantitative original-port density estimate on the fixed common event. -/
noncomputable section
namespace LooseHamilton.BootstrapPortCommonDensity
open Finset Filter BootstrapBases BootstrapCatalogue BootstrapConstants SequentialCompletion
open BootstrapPortDensityScales
variable {N r : ℕ} {M : Finset (Finset (Fin N))}

/-- All forbidden-port losses use the actual matching size, not its upper envelope. -/
theorem explicit_density (hr : 3 ≤ r) (hN : 2*r ≤ N)
    (ha : 0 ≤ FrameScales.alpha N) (ha1 : FrameScales.alpha N ≤ 1)
    (hM : IsPairMatching M) (H J : SimpleHypergraph (Fin N))
    (hH : H ⊆ completeEdges (Fin N) r) (X c : ℝ) (hc : 0<c)
    (hb : ∀ b : Base M, BootstrapSequentialMobility.Bounds (r:=r) hM b H X c)
    (h time : ℕ) (P : Finset (Fin N)) (y z u : Fin N)
    (hs : LegalPrivateCompletion r (M.erase {y,z}) P {u,z})
    (hy : y ∉ P ∪ {u,z}) (hm : {y,z} ∈ M) (hyz : y ≠ z)
    (hlarge : X/(N:ℝ)^(2*r) ≤
      (rootFreePortSource r M (fixedPortHost H (originalPorts M)) y z P u:ℝ)) :
    rootLinkDensity r y ((registerPortRootTest r h time M (originalPorts M) P y z u
      (portThreshold r c)).badSet (J,H)) ≤
      densityConstant r*(FrameScales.alpha N)^(1/4:ℝ)+
        densityConstant r*((M.card:ℝ)+1)/(N:ℝ) := by
  let a : ↥(originalPorts M) := ⟨y,BootstrapPortSourceGeometry.chosen_port_mem hm⟩
  have hp : (fixedPorts (some a)).card ≤ 2*M.card := by
    rw [←hM.ports_card]
    apply card_le_card_of_injOn Subtype.val
    · intro v hv; exact (mem_fixedPorts (some a) v).mp hv
    · intro v hv w hw he; exact Subtype.ext he
  have hq : ((originalPorts M).erase y).card ≤ 2*M.card := by
    rw [←hM.ports_card]; exact card_erase_le
  have hn := actual_density_bound (r:=r) (by omega : 2≤N) hp hq ha ha1
  have hd := BootstrapPortFiniteDensity.density_le hr hN ha hM H J hH X c hc hb
    h time P y z u hs hy hm hyz hlarge
  apply hd.trans
  convert hn using 1 <;> dsimp [countingCoefficient] <;> ring

/-- Uniform over cores, times and all actual original-port sources. The test
registry is fixed before observing the host, and all density gates are derived. -/
theorem eventually_port_density (r : ℕ) (hr : 3 ≤ r) (c : ℝ) (hc : 0<c) :
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
      (X:ℝ)/(N:ℝ)^(2*r) ≤ (rootFreePortSource r M
        (fixedPortHost H (originalPorts M)) y z P u:ℝ) →
      rootLinkDensity r y ((registerPortRootTest r hR j M (originalPorts M) P y z u
        (portThreshold r c)).badSet (ω.1.val,H)) < FrameScales.rho N := by
  filter_upwards [BootstrapSequentialMobility.eventually_sequential_mobility r hr c hc,
    eventually_explicit_density_lt_rho r,
    BootstrapPrivateMobilityScales.eventually_private_mobility_bounds r hr]
    with N hseq hdensity hsc
  intro m ell M offset hadm
  obtain ⟨hroom,hseq⟩ := hseq m ell M offset hadm
  refine ⟨hroom,?_⟩
  intro h hR C L ω hω j hj hK H X hX hAX P y z u hs hy hm hyz hlarge
  have hb := hseq h hR (portThreshold r c) C L ω hω j hj hK hX hAX
  have hN : 2*r ≤ N := by have := hsc.1; omega
  have hh := explicit_density hr hN hsc.2.1.le (by have := hsc.2.2.1; linarith)
    hadm.marker_matching H ω.1.val (extensionState_subset ω.1 ω.2 j) X c hc hb
    hR j P y z u hs hy hm hyz hlarge
  exact hh.trans_lt (hdensity M.card (by simpa using hadm.markers_small))

end LooseHamilton.BootstrapPortCommonDensity
