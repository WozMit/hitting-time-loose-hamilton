module

public import HittingTimeLooseHamilton.BootstrapPrivateCommonEvent
public import HittingTimeLooseHamilton.BootstrapSourceEligibility
public import HittingTimeLooseHamilton.BootstrapMaximumMeans
public import HittingTimeLooseHamilton.BootstrapMobilityConstants
public import HittingTimeLooseHamilton.PortRootEventCap

public section

noncomputable section
namespace LooseHamilton.BootstrapPortCap
open Finset Filter BootstrapCatalogue BootstrapConstants RootFreeTestIndexing

/-- Uniform constant for both negligible and sampled original-port sources. -/
@[expose] def constant (r : ℕ) (c : ℝ) : ℝ := max (r:ℝ) (3/(portThreshold r c*c))

theorem constant_pos {r : ℕ} (hr : 3 ≤ r) (c : ℝ) : 0 < constant r c := by
  exact (Nat.cast_pos.mpr (show 0<r by omega)).trans_le (le_max_left _ _)


/-- The third literal registered test passes on the fixed common event as soon
as its proved density estimate is available. -/
theorem nonfailure {N r m h hR : ℕ} {ell : Fin N → ℕ}
    {M : Finset (Finset (Fin N))} (hM : IsPairMatching M) (hr : 3 ≤ r)
    (hroom : 2*M.card+2 ≤ Fintype.card (Fin N))
    (cP cE cPort c C L : ℝ) (hc : 0 ≤ c)
    (ω : CandidateBalance.Outcome (Fin N) r m ell)
    (hω : RootFreeCommonEvent (fixedRegistry (h:=hR) hM hr hroom cP cE cPort)
      h c C L 2 (rootConstant c) ω)
    (hmean : Real.log (Fintype.card (Fin N):ℝ)/2 ≤ meanDegree (V:=Fin N) r m)
    (P : Finset (Fin N)) (hP : P.card=r-2) (y z u : Fin N)
    (hs : LegalPrivateCompletion r (M.erase {y,z}) P {u,z})
    (hy : y ∉ P ∪ {u,z}) (hyz : y ≠ z)
    (j : Fin ((Fintype.card (Fin N))^r+1)) (hj : m ≤ j.val)
    (hK : j.val ≤ (completeEdges (Fin N) r).card)
    (hdensity : rootLinkDensity r y
      ((registerPortRootTest r hR j.val M (originalPorts M) P y z u cPort).badSet
        (ω.1.val,extensionState ω.1 ω.2 j.val)) ≤ FrameScales.rho N) :
    ¬ RootLinkBad
      ((registerPortRootTest r hR j.val M (originalPorts M) P y z u cPort).badSet
        (ω.1.val,extensionState ω.1 ω.2 j.val))
      (vertexDegree (extensionState ω.1 ω.2 j.val) y)
      (ω.1.val,extensionState ω.1 ω.2 j.val) := by
  let l : PortLabel r (Fin N) := (⟨P,mem_powersetCard.mpr ⟨subset_univ _,hP⟩⟩,y,z,u)
  have he := tests_port (h:=hR) hM cP cE cPort l j
    (port_sourceDistinct_of_legal M ⟨P,mem_powersetCard.mpr ⟨subset_univ _,hP⟩⟩ y z u hs hy hyz)
  have hn := BootstrapPrivateCommonEvent.catalogue_nonfailure hM hr hroom cP cE cPort
    c C L hc ω hω hmean (portIndex l j) hj hK
  rw [he] at hn
  simp only [Fintype.card_fin] at hn
  change (rootLinkDensity r y
    ((registerPortRootTest r hR j.val M (originalPorts M) P y z u cPort).badSet
      (rootFreePairObservation r m ell j.val y ω)) ≤ FrameScales.rho N) → _ at hn
  have ho := registerPortRootTest_observation r hR j.val M ω.1.val
    (extensionState ω.1 ω.2 j.val) (originalPorts M) P y z u cPort
  change (registerPortRootTest r hR j.val M (originalPorts M) P y z u cPort).badSet
    (rootFreePairObservation r m ell j.val y ω) = _ at ho
  rw [ho] at hn
  have hh := hn hdensity
  change ¬RootLinkBad
    ((registerPortRootTest r hR j.val M (originalPorts M) P y z u cPort).badSet
      (rootFreePairObservation r m ell j.val y ω))
    (j.val-(rootFreePairObservation r m ell j.val y ω).2.card)
    (rootSamplingPair r m ell j.val ω) at hh
  rw [ho,sampling_degree_eq ω hj hK] at hh
  exact hh

/-- The exact contraction partition and raw lower degree bound yield the cap
with the same raw mean used by the ordinary-label branch. -/
theorem source_cap {N r : ℕ} (hr : 3 ≤ r)
    (M F H : SimpleHypergraph (Fin N)) (hM : IsPairMatching M)
    (hH : H ⊆ completeEdges (Fin N) r) (hsize : 5*(r-1)<N)
    (h time : ℕ) (c : ℝ) (hc : 0<c)
    (hmu : 0 < meanDegree (V:=Fin N) r H.card)
    (P : Finset (Fin N)) (y z u : Fin N) (hyz : y≠z) (hm : {y,z}∈M)
    (hdegree : c*meanDegree (V:=Fin N) r H.card ≤ (vertexDegree H y:ℝ))
    (hn : ¬RootLinkBad
      ((registerPortRootTest r h time M (originalPorts M) P y z u (portThreshold r c)).badSet (F,H))
      (vertexDegree H y) (F,H)) :
    (rootFreePortSource r M (fixedPortHost H (originalPorts M)) y z P u:ℝ) ≤
      constant r c*(cycleCount r M H (originalPorts M):ℝ)/meanDegree (V:=Fin N) r H.card := by
  have ht := portThreshold_pos hr hc
  have hb := port_source_bound_of_registered_test hr h time M F H P y z u hyz hm
    hM.2 hH (by simpa using hsize) (portThreshold r c) ht.le hn
  have hf : fixedPortHost H (originalPorts M) = H ∩ allowedEdges r (originalPorts M) := by
    ext e
    simp only [fixedPortHost,mem_filter,mem_inter,mem_allowedEdges]
    constructor
    · rintro ⟨he,hp⟩; exact ⟨he,(mem_completeEdges _ _).mp (hH he),hp⟩
    · rintro ⟨he,_,hp⟩; exact ⟨he,hp⟩
  rw [hf, ←cycleCount_eq_unrestricted_inter r M H (originalPorts M) hr] at hb
  have hstep := mul_le_mul_of_nonneg_right hdegree
    (mul_nonneg (div_nonneg ht.le (by norm_num : (0:ℝ) ≤ 3))
      (Nat.cast_nonneg (rootFreePortSource r M (H ∩ allowedEdges r (originalPorts M)) y z P u)))
  have hbound : (rootFreePortSource r M (fixedPortHost H (originalPorts M)) y z P u:ℝ) ≤
      (3/(portThreshold r c*c))*(cycleCount r M H (originalPorts M):ℝ)/meanDegree (V:=Fin N) r H.card := by
    rw [hf]
    apply (le_div_iff₀ hmu).mpr
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (mul_pos ht hc)).mpr
    nlinarith
  exact hbound.trans (div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right (le_max_right _ _) (Nat.cast_nonneg _)) hmu.le)

/-- Negligible contractions are covered by the elementary uniform-host mean
bound; only non-negligible contractions require a root-test implication. -/
theorem source_cap_including_tiny {N r : ℕ} (hr : 3 ≤ r) (hN : 1 ≤ N)
    (M F H : SimpleHypergraph (Fin N)) (hM : IsPairMatching M)
    (hH : H ⊆ completeEdges (Fin N) r) (hsize : 5*(r-1)<N)
    (h time : ℕ) (c : ℝ) (hc : 0<c)
    (hmu : 0 < meanDegree (V:=Fin N) r H.card)
    (P : Finset (Fin N)) (y z u : Fin N) (hyz : y≠z) (hm : {y,z}∈M)
    (hdegree : c*meanDegree (V:=Fin N) r H.card ≤ (vertexDegree H y:ℝ))
    (hn : (cycleCount r M H (originalPorts M):ℝ)/(N:ℝ)^(2*r) ≤
        (rootFreePortSource r M (fixedPortHost H (originalPorts M)) y z P u:ℝ) →
      ¬RootLinkBad
        ((registerPortRootTest r h time M (originalPorts M) P y z u (portThreshold r c)).badSet (F,H))
        (vertexDegree H y) (F,H)) :
    (rootFreePortSource r M (fixedPortHost H (originalPorts M)) y z P u:ℝ) ≤
      constant r c*(cycleCount r M H (originalPorts M):ℝ)/meanDegree (V:=Fin N) r H.card := by
  by_cases hlarge : (cycleCount r M H (originalPorts M):ℝ)/(N:ℝ)^(2*r) ≤
      (rootFreePortSource r M (fixedPortHost H (originalPorts M)) y z P u:ℝ)
  · exact source_cap hr M F H hM hH hsize h time c hc hmu P y z u hyz hm hdegree (hn hlarge)
  · have hsmall := le_of_lt (lt_of_not_ge hlarge)
    have htiny := BootstrapMaximumMeans.tiny_source_le (by omega : 1≤r) hN H hH hmu
      (cycleCount r M H (originalPorts M):ℝ) (Nat.cast_nonneg _)
    exact hsmall.trans (htiny.trans (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (Nat.cast_nonneg _)) hmu.le))

end LooseHamilton.BootstrapPortCap
