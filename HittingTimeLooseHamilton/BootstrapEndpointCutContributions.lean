module

public import HittingTimeLooseHamilton.BootstrapEndpointDensityTargets
public import HittingTimeLooseHamilton.BootstrapEndpointRegistryCoverage
public import HittingTimeLooseHamilton.BootstrapEndpointCommonEvent
public import HittingTimeLooseHamilton.BootstrapEndpointMobilityScales
public import HittingTimeLooseHamilton.BootstrapEndpointCutParameters
public import HittingTimeLooseHamilton.LiftedEndpointMobility
public import HittingTimeLooseHamilton.BootstrapTagRoom

public section

/-! Uniform per-cut endpoint density and actual directed contributions on the
fixed common event. Actual core balance is derived from the retained cutoff. -/
noncomputable section
namespace LooseHamilton.BootstrapEndpointCutContributions
open Finset Filter BootstrapBases BootstrapCatalogue BootstrapEndpointCutParameters

/-- Finite composition; the eventual theorem discharges its intermediate gates. -/
theorem of_candidates {N r m h hR : ℕ} {ell : Fin N → ℕ}
    {original : SimpleHypergraph (Fin N)} (hM : IsPairMatching original) (hr : 3 ≤ r)
    (hroom : 2*original.card+2 ≤ Fintype.card (Fin N))
    (cP cPort c C L : ℝ) (hc : 0 ≤ c)
    (ω : CandidateBalance.Outcome (Fin N) r m ell)
    (hω : RootFreeCommonEvent
      (fixedRegistry (h := hR) hM hr hroom cP (BootstrapConstants.rootThreshold r) cPort)
      h c C L 2 (rootConstant c) ω)
    (hmean : Real.log (Fintype.card (Fin N):ℝ)/2 ≤ meanDegree (V := Fin N) r m)
    (j : ℕ) (hj : m ≤ j) (hK : j ≤ (completeEdges (Fin N) r).card)
    (b : Base original) (P : Finset ↥(active b)) (y z : ↥(active b))
    (hs : LegalPrivateCompletion r (restrictEdges (active b) (markers hM b)) P {y,z})
    (k : EndpointMigrationCut r (restrictEdges (active b) (markers hM b))
      (fixedPortHost (inducedHost (active b) (extensionState ω.1 ω.2 j)) (fixedPorts b)) P y z)
    (F : AuxiliaryFrame.Frame r original)
    (hshape : BootstrapEndpointLiftedBadSet.CoreShape hM b P y z (endpointMigrationRawLabel k) F)
    (hX : 0 < rootFreeEndpointX r (restrictEdges (active b) (markers hM b))
      (fixedPortHost (inducedHost (active b) (extensionState ω.1 ω.2 j)) (fixedPorts b)) P y z
      (endpointMigrationRawLabel k))
    (hbalance : ¬ F.candidateBad (extensionState ω.1 ω.2 j) (FrameScales.alpha N))
    (hN : 8*r ≤ N) (ha : 0 < FrameScales.alpha N) (hahalf : FrameScales.alpha N ≤ 1/2)
    (hdens : (2:ℝ)^(r-1)*((r-1).factorial:ℝ)*Real.sqrt (FrameScales.alpha N)+
      (2*original.card+3*r+2:ℕ)*(r-1:ℕ)/(N-1:ℕ) < FrameScales.rho N)
    (hsize : Real.sqrt (FrameScales.alpha N)*N+(2*original.card+3*r+2:ℕ) ≤
      2*Real.sqrt (FrameScales.alpha N)*N) :
    ∃ E : Finset (Fin N), (E.card:ℝ) ≤ 2*Real.sqrt (FrameScales.alpha N)*N ∧
      ∀ t : ↥(active b), t.val ∉ E →
      rootLinkDensity r y.val (BootstrapEndpointLiftedBadSet.registeredBadSet r hR j hM b
        P y z t (endpointMigrationRawLabel k) (rootFreeEdges y.val ω.1.val)
          (rootFreeEdges y.val (extensionState ω.1 ω.2 j))) < FrameScales.rho N ∧
      BootstrapConstants.privateFactor r c*endpointMigrationWeight k ≤
        ∑ q ∈ endpointMigrationLabels t k, endpointMigrationY t k q := by
  let H := extensionState ω.1 ω.2 j
  have hH := extensionState_subset ω.1 ω.2 j
  have hN' : 8*r ≤ Fintype.card (Fin N) := by simpa using hN
  have hcut := BootstrapEndpointComparison.cut_deleted_card_le hr _ _ P y z _ (raw_legal k)
  obtain ⟨E,hDE,hE,htest⟩ := BootstrapEndpointDensityTargets.exists_density_targets hM b F hr
    H hH P y z _ hshape hs.private_card hcut hX _ ha hahalf (by omega) hbalance
  refine ⟨E,?_,?_⟩
  · simp only [Fintype.card_fin] at hE
    exact hE.trans hsize
  intro t ht
  have hd := (htest t ht).2 hR j ω.1.val
  simp only [Fintype.card_fin] at hd
  have hd' := hd.trans_lt hdens
  refine ⟨hd',?_⟩
  have hjbound : j < (Fintype.card (Fin N))^r+1 := by
    have hk := Nat.choose_le_pow N r
    simp only [completeEdges_card,Fintype.card_fin] at hK ⊢
    omega
  have hn := BootstrapEndpointRegistryCoverage.endpoint_nonfailure_actual hM hr hroom cP cPort
    c C L hc ω hω hmean b _ P hs.private_card y z t hs k ⟨j,hjbound⟩ hj hK
    (by simpa only [Fintype.card_fin,rootFreePairObservation,H] using hd'.le)
  have hsub : fixedPortHost (inducedHost (active b) H) (fixedPorts b) ⊆ inducedHost (active b) H :=
    filter_subset _ _
  have hμ := rootFreeEndpointMean_pos_of_source (endpointMigrationRawLabel k) (by omega : 0 < r) hsub hX
  have hratio := BootstrapMeans.endpoint_degree_mean_ratio hr b H P y z
    (endpointMigrationRawLabel k) (restrictEdges (active b) (markers hM b))
    (fixedPortHost (inducedHost (active b) H) (fixedPorts b)) hs.private_card (by
      cases k with
      | inl k => exact ((mem_endpointCutLabelsI _ _ _ _ _ _ _).mp k.property).private_card
      | inr k =>
        have hl := (mem_endpointCutLabelsII _ _ _ _ _ _ _).mp k.property
        exact ⟨hl.first_private_card,hl.second_private_card⟩) hN'  hsub hX hc (hω.1.2.1 j hj hK)
  exact endpoint_cut_fixed_factor_of_lifted_root_test r hR j (deleted b) _ ω.1.val H P
    (fixedPorts b) y z t k c hr hμ hH hratio ∅ (empty_subset _) (by simp) hn

/-- A single threshold covers all retained cuts, times, outcomes and bases.
No core frame, entropy budget, candidate balance, density or occupancy premise
remains in this final per-cut theorem. -/
theorem eventually_cut_contributions (r : ℕ) (hr : 3 ≤ r) :
    ∀ᶠ N : ℕ in atTop, ∀ (m : ℕ) (ell : Fin N → ℕ)
      (original : SimpleHypergraph (Fin N)) (offset : ℝ)
      (hadm : CoreAdmissible r m ell original offset),
      ∃ hroom : 2*original.card+2 ≤ Fintype.card (Fin N),
      ∀ (h hR : ℕ) (cP cPort c C L : ℝ), 0 < c →
      ∀ ω : CandidateBalance.Outcome (Fin N) r m ell,
      RootFreeCommonEvent
        (fixedRegistry (h := hR) hadm.marker_matching hr hroom cP (BootstrapConstants.rootThreshold r) cPort)
        h c C L 2 (rootConstant c) ω →
      ∀ j : ℕ, m ≤ j → j ≤ (completeEdges (Fin N) r).card →
      let H := extensionState ω.1 ω.2 j
      let X := cycleCount r original H (originalPorts original)
      0 < X → logarithmicBaseline r (ordinaryEdgeCount r original) j original -
        (N:ℝ)/Real.sqrt (Real.log N) ≤ Real.log (X:ℝ) →
      ∀ (b : Base original) (P : Finset ↥(active b)) (y z : ↥(active b)),
      LegalPrivateCompletion r (restrictEdges (active b) (markers hadm.marker_matching b)) P {y,z} →
      ∀ k : EndpointMigrationCut r (restrictEdges (active b) (markers hadm.marker_matching b))
        (fixedPortHost (inducedHost (active b) H) (fixedPorts b)) P y z,
      (X:ℝ)/(N:ℝ)^(5*r+2) ≤ endpointMigrationWeight k →
      ∃ E : Finset (Fin N), (E.card:ℝ) ≤ 2*Real.sqrt (FrameScales.alpha N)*N ∧
        ∀ t : ↥(active b), t.val ∉ E →
        rootLinkDensity r y.val (BootstrapEndpointLiftedBadSet.registeredBadSet r hR j
          hadm.marker_matching b P y z t (endpointMigrationRawLabel k)
          (rootFreeEdges y.val ω.1.val) (rootFreeEdges y.val H)) < FrameScales.rho N ∧
        BootstrapConstants.privateFactor r c*endpointMigrationWeight k ≤
          ∑ q ∈ endpointMigrationLabels t k, endpointMigrationY t k q := by
  filter_upwards [BootstrapEndpointMobilityScales.eventually_endpoint_mobility_bounds r hr,
    BootstrapEndpointCommonEvent.eventually_admissible_core_candidates r hr,
    eventually_terminal_mean_lower, BootstrapTagFrames.eventually_admissible_tag_room]
    with N hsc hcan hmean hroom
  intro m ell original offset hadm
  have hroom' : 2*original.card+2 ≤ Fintype.card (Fin N) := by
    simpa using hroom r m ell original offset hadm
  refine ⟨hroom',?_⟩
  intro h hR cP cPort c C L hc ω hω j hj hK H X hX hAX b P y z hs k hlarge
  obtain ⟨F,hshape⟩ := BootstrapEndpointComparison.exists_core hadm.marker_matching b hr _ P y z
    (endpointMigrationRawLabel k) hs (raw_legal k)
  have hcut : (X:ℝ)/(N:ℝ)^(5*r+2) ≤ rootFreeEndpointX r
      (restrictEdges (active b) (markers hadm.marker_matching b))
      (fixedPortHost (inducedHost (active b) H) (fixedPorts b)) P y z (endpointMigrationRawLabel k) := by
    rw [endpointMigration_rootFree_X]
    exact hlarge
  have hN : 0 < N := by have := hsc.1; omega
  have hpos := BootstrapEndpointCommonEvent.positive_core_of_cutoff hN hX hcut
  have hbalance := hcan m ell original offset hadm h hR c C L (rootConstant c) _ ω hω
    j hj hK hX hAX b F P y z _ hshape hcut
  have hb := hsc.2.2.2.2 original.card (by simpa using hadm.markers_small)
  have hm : Real.log (Fintype.card (Fin N):ℝ)/2 ≤ meanDegree (V := Fin N) r m := by
    simpa using hmean r m ell original offset hadm
  apply of_candidates hadm.marker_matching hr hroom' cP cPort c C L hc.le ω hω hm j hj hK
    b P y z hs k F hshape hpos hbalance hsc.1 hsc.2.1 hsc.2.2.1
  · apply lt_of_le_of_lt _ hb.1
    apply add_le_add_right
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right
      (Nat.cast_le.mpr (by omega : 2*original.card+3*r+2 ≤ 2*original.card+3*r+4))
      (Nat.cast_nonneg _)) (Nat.cast_nonneg _)
  · exact (add_le_add_right (Nat.cast_le.mpr
      (by omega : 2*original.card+3*r+2 ≤ 2*original.card+3*r+4)) _).trans hb.2

end LooseHamilton.BootstrapEndpointCutContributions
