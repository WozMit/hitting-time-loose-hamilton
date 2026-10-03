module

public import HittingTimeLooseHamilton.BootstrapOrdinaryFailedLabels
public import HittingTimeLooseHamilton.BootstrapOriginalBalance

public section

/-! Uniform completion maximum for labels avoiding the original ports. -/
noncomputable section
set_option maxHeartbeats 1200000
namespace LooseHamilton.BootstrapOrdinaryMaximum
open Finset Filter AuxiliaryFrame BootstrapCatalogue BootstrapConstants BootstrapCompletionMaximum

@[expose] def constant (r : ℕ) (c : ℝ) : ℝ :=
  max (r:ℝ) (6/((privateFactor r c^(r-2)*endpointFactor r c^2)*((r:ℝ)-1)^2))

theorem eventually_completion_maximum (r : ℕ) (hr : 3 ≤ r) (c C : ℝ)
    (hc : 0<c) (hC : 0≤C) :
    ∀ᶠ N : ℕ in atTop, ∀ (m : ℕ) (ell : Fin N → ℕ)
      (M : Finset (Finset (Fin N))) (offset : ℝ)
      (hadm : CoreAdmissible r m ell M offset),
      ∃ hroom : 2*M.card+2 ≤ Fintype.card (Fin N),
      ∀ (h hR : ℕ) (cPort L : ℝ)
        (ω : CandidateBalance.Outcome (Fin N) r m ell),
      RootFreeCommonEvent
        (fixedRegistry (h:=hR) hadm.marker_matching hr hroom
          (rootThreshold r) (rootThreshold r) cPort)
        h c C L 2 (rootConstant c) ω →
      ∀ j : ℕ, m ≤ j → j ≤ (completeEdges (Fin N) r).card →
      let H := extensionState ω.1 ω.2 j
      let X := cycleCount r M H (originalPorts M)
      0 < X → logarithmicBaseline r (ordinaryEdgeCount r M) j M -
        (N:ℝ)/Real.sqrt (Real.log N) ≤ Real.log (X:ℝ) →
      ∀ (P : Finset (Fin N)) (y z : Fin N), LegalPrivateCompletion r M P {y,z} →
      (completionCount r M (H ∩ allowedEdges r (originalPorts M)) P {y,z}:ℝ) ≤
        constant r c*(X:ℝ)/meanDegree (V:=Fin N) r j := by
  classical
  filter_upwards [BootstrapSequentialMobility.eventually_sequential_mobility r hr c hc,
    BootstrapOriginalBalance.eventually_original_balance r hr,
    BootstrapMaximumMeans.eventually_original_mean_lower r C hC,
    BootstrapMaximumIntersection.eventually_error_intersection r (by omega),
    BootstrapPrivateMobilityScales.eventually_private_mobility_bounds r hr] with N hseq hbal hmean hint hsc
  intro m ell M offset hadm
  obtain ⟨hroom,hseq⟩ := hseq m ell M offset hadm
  refine ⟨hroom,?_⟩
  intro h hR cPort L ω hω j hj hK H X hX hAX P y z hs
  obtain ⟨F,hd,hm,hrel⟩ := exists_original_frame (r:=r) hadm.marker_matching
    (card_pos.mp (by have := hadm.markers_nonempty; omega))
  have hsmall : (M.card:ℝ) ≤ (N:ℝ)^(1/10:ℝ) := by simpa using hadm.markers_small
  have hN : 0<N := by have := hsc.1; omega
  have hH : H ⊆ completeEdges (Fin N) r := extensionState_subset ω.1 ω.2 j
  have hcard : H.card=j := extensionState_card ω.1 ω.2 j hj hK
  have hreg := hω.1.2.1 j hj hK
  have hmean' := hmean hadm.marker_matching hsmall F hd H hH hreg.upper_degree
  have hmuF : 0 < F.mu H := F.mu_pos_of_cycleCount_pos hr H (by
    rw [F.original_cycleCount hr hrel hd hm H]; exact hX)
  have hmu : 0 < meanDegree (V:=Fin N) r H.card := by
    have hle := (F.mu_le_outer_inducedMean H).trans (BootstrapMeans.inducedMean_le r H F.active)
    have hn : F.active.card=N := by simp [Frame.active,Code.active,hd]
    rw [hn] at hle
    exact hmuF.trans_le (by simpa only [meanDegree,Fintype.card_fin] using hle)
  have hbalance := hbal m ell M offset hadm h hR c C L (rootConstant c) _ ω hω
    j hj hK hX hAX F hd hm hrel
  let κ := privateFactor r c^(r-2)*endpointFactor r c^2
  have hκ : 0<κ := mul_pos (pow_pos (privateFactor_pos hr hc) _) (pow_pos (endpointFactor_pos hr hc) _)
  have hbound := all_weights_le_of_failed_labels F hr (by omega) hd hm hrel H hH
    (FrameScales.alpha N) κ ((r:ℝ)*BootstrapMaximumIntersection.error r N*(N:ℝ)^r)
    hκ hX hsc.2.2.1 hmu hmean' hbalance
    (fun a ha hlarge => BootstrapOrdinaryFailedLabels.failed_labels hr hN hadm.marker_matching
      hsmall F hm H hH X c (hseq h hR cPort C L ω hω j hj hK hX hAX none) a ha hlarge)
    (hint hadm.marker_matching hsmall F hd)
  have hlegal : (P,y,z) ∈ F.candidates := by
    apply mem_filter.mpr
    refine ⟨mem_univ _,?_,?_,?_⟩
    · simpa only [hm] using hs
    · simp [Frame.active,Code.active,hd]
    · rw [mem_allowedEdges]
      constructor
      · rw [card_union_of_disjoint hs.private_pair_disjoint,hs.private_card,hs.pair_card]; omega
      · rw [disjoint_iff_inter_eq_empty.mp hs.ports_disjoint]; simp
  have hh := hbound (P,y,z) hlegal
  simpa only [weight,constant,κ,hcard] using hh

end LooseHamilton.BootstrapOrdinaryMaximum
