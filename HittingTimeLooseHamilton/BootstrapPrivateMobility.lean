module

public import HittingTimeLooseHamilton.BootstrapPrivateMobilityScales
public import HittingTimeLooseHamilton.BootstrapPrivateRegistryCoverage
public import HittingTimeLooseHamilton.BootstrapPrivateAdmissibleParameters
public import HittingTimeLooseHamilton.BootstrapPrivateDensityTargets
public import HittingTimeLooseHamilton.BootstrapNormalizedPrivateSources
public import HittingTimeLooseHamilton.LiftedPrivateMobility
public import HittingTimeLooseHamilton.BootstrapTagRoom

public section

/-! Private mobility for every legal large source on the fixed common event.
The eventual threshold precedes the core, outcome, time, base and source labels. -/
noncomputable section
namespace LooseHamilton.BootstrapPrivateMobility
open Finset Filter BootstrapBases BootstrapCatalogue

/-- The literal residual private completion count, with original ports fixed. -/
@[expose] def sourceCount {V : Type} [Fintype V] [DecidableEq V] (r : ℕ)
    {original : Finset (Finset V)} (hM : IsPairMatching original) (b : Base original)
    (H : SimpleHypergraph V) (S q : Finset ↥(active b)) (x : ↥(active b)) : ℕ :=
  completionCount r (restrictEdges (active b) (markers hM b))
    (fixedPortHost (inducedHost (active b) H) (fixedPorts b)) (insert x S) q

/-- Explicit exceptional-set conclusion, with a constant independent of the source. -/
@[expose] def Mobility {N r : ℕ} {original : Finset (Finset (Fin N))}
    (hM : IsPairMatching original) (b : Base original) (H : SimpleHypergraph (Fin N))
    (S q : Finset ↥(active b)) (x : ↥(active b)) (c : ℝ) : Prop :=
  ∃ E : Finset (Fin N), deleted b ⊆ E ∧
    (E.card:ℝ) ≤ (Real.sqrt (r-2:ℕ)+1)*Real.sqrt (FrameScales.alpha N)*N ∧
    ∀ t : ↥(active b), t.val ∉ E →
      LegalPrivateCompletion r (restrictEdges (active b) (markers hM b)) (insert t S) q ∧
      BootstrapConstants.privateFactor r c * (sourceCount r hM b H S q x:ℝ) ≤
        sourceCount r hM b H S q t

/-- Composition at fixed size. The uniform theorem discharges the intermediate gates. -/
theorem of_candidates {N r m h hR : ℕ} {ell : Fin N → ℕ}
    {original : Finset (Finset (Fin N))} (hM : IsPairMatching original) (hr : 3 ≤ r)
    (hroom : 2*original.card+2 ≤ Fintype.card (Fin N))
    (cE cPort c C L : ℝ) (hc : 0 ≤ c)
    (ω : CandidateBalance.Outcome (Fin N) r m ell)
    (hω : RootFreeCommonEvent
      (fixedRegistry (h := hR) hM hr hroom (BootstrapConstants.rootThreshold r) cE cPort)
      h c C L 2 (rootConstant c) ω)
    (hmean : Real.log (Fintype.card (Fin N) : ℝ)/2 ≤ meanDegree (V := Fin N) r m)
    (j : ℕ) (hj : m ≤ j) (hK : j ≤ (completeEdges (Fin N) r).card)
    (b : Base original) (S q : Finset ↥(active b)) (x : ↥(active b))
    (hS : S.card = r-3)
    (hs : LegalPrivateCompletion r (restrictEdges (active b) (markers hM b)) (insert x S) q)
    (F : AuxiliaryFrame.Frame r original)
    (hd : F.val.deleted = deleted b ∪ liftEdge (active b) (insert x S))
    (hm : F.markers = insert (liftEdge (active b) q) (markers hM b))
    (hrel : F.val.relative = none)
    (hW : 0 < sourceCount r hM b (extensionState ω.1 ω.2 j) S q x)
    (hbalance : ¬ F.candidateBad (extensionState ω.1 ω.2 j) (FrameScales.alpha N))
    (hN : 8*r ≤ N) (ha : 0 < FrameScales.alpha N) (hahalf : FrameScales.alpha N ≤ 1/2)
    (hdens : (2:ℝ)^(r-1)*((r-1).factorial:ℝ)*Real.sqrt ((r-2:ℕ)*FrameScales.alpha N) +
      (2*original.card+r+1:ℕ)*(r-1:ℕ)/(N-1:ℕ) < FrameScales.rho N)
    (hsize : Real.sqrt ((r-2:ℕ)*FrameScales.alpha N)*N+(2*original.card+r+1:ℕ) ≤
      (Real.sqrt (r-2:ℕ)+1)*Real.sqrt (FrameScales.alpha N)*N) :
    Mobility (r := r) hM b (extensionState ω.1 ω.2 j) S q x c := by
  let H := extensionState ω.1 ω.2 j
  have hH := extensionState_subset ω.1 ω.2 j
  have hN' : 8*r ≤ Fintype.card (Fin N) := by simpa using hN
  have hn := BootstrapPrivateSourceNormalization.normalized_source_bounds hM b F hr H hH
    S q x hd hm hrel hW hS hN' hc (hω.1.2.1 j hj hK)
  refine ⟨BootstrapPrivateDensityTargets.excludedTargets b F H S q x (FrameScales.alpha N),
    BootstrapPrivateDensityTargets.deleted_subset_excluded b F H S q x _, ?_, ?_⟩
  · have hb := BootstrapPrivateDensityTargets.excluded_card_le hM hr b F H S q x hS
      hs.pair_card _ ha hbalance (by simp only [Fintype.card_fin]; omega)
    simp only [Fintype.card_fin] at hb
    exact hb.trans hsize
  intro t ht
  have htgeom : t.val ∉ BootstrapPrivateLinkGeometry.exclusions b S q x :=
    fun ht' => ht (mem_union_right _ ht')
  have htarget := (BootstrapPrivateLinkGeometry.target_legal hM hr b S q x t hS hs htgeom).2.2
  refine ⟨htarget,?_⟩
  have hden := BootstrapPrivateDensityTargets.density_of_not_excluded hR j hM b F hr
    ω.1.val H hH S q x t hS hs hd hm hrel hW _ hahalf (by omega) ht
  have hdensity : rootLinkDensity r x.val
      (BootstrapPrivateLiftedBadSet.registeredBadSet r hR j hM b S q x t
        (rootFreeEdges x.val ω.1.val) (rootFreeEdges x.val H)) ≤ FrameScales.rho N :=
    by
    simp only [Fintype.card_fin] at hden
    exact hden.trans hdens.le
  obtain ⟨y,z,hyz,hq⟩ := card_eq_two.mp hs.pair_card
  have hjbound : j < (Fintype.card (Fin N))^r+1 := by
    have hk := Nat.choose_le_pow N r
    simp only [completeEdges_card,Fintype.card_fin] at hK ⊢
    omega
  have htest := BootstrapPrivateCommonEvent.private_nonfailure hM hr hroom cE cPort c C L
    hc ω hω hmean b S hS x y z t (by simpa only [hq] using hs)
    ⟨j,hjbound⟩ hj hK (by simpa only [hq,Fintype.card_fin,rootFreePairObservation,H] using hdensity)
  rw [← hq, sampling_degree_eq ω hj hK x.val] at htest
  change ¬ RootLinkBad (BootstrapPrivateLiftedBadSet.registeredBadSet r hR j hM b S q x t
    (rootFreeEdges x.val ω.1.val) (rootFreeEdges x.val H)) (vertexDegree H x.val) (ω.1.val,H) at htest
  rw [BootstrapPrivateLiftedBadSet.observation_eq] at htest
  exact private_fixed_factor_of_lifted_root_test r hR j (deleted b) _ ω.1.val H S q
    (fixedPorts b) x t c hr hH htarget hn.2.2.1 hn.2.2.2.2 htest

/-- Uniform private mobility for all r ≥ 3 and both bases. No frame, entropy
budget, balance, density or sampling gate is assumed. -/
theorem eventually_private_mobility (r : ℕ) (hr : 3 ≤ r) :
    ∀ᶠ N : ℕ in atTop, ∀ (m : ℕ) (ell : Fin N → ℕ)
      (original : Finset (Finset (Fin N))) (offset : ℝ)
      (hadm : CoreAdmissible r m ell original offset),
      ∃ hroom : 2*original.card+2 ≤ Fintype.card (Fin N),
      ∀ (h hR : ℕ) (cE cPort c C L : ℝ), 0 < c →
      ∀ (ω : CandidateBalance.Outcome (Fin N) r m ell),
      RootFreeCommonEvent
        (fixedRegistry (h := hR) hadm.marker_matching hr hroom
          (BootstrapConstants.rootThreshold r) cE cPort)
        h c C L 2 (rootConstant c) ω →
      ∀ j : ℕ, m ≤ j → j ≤ (completeEdges (Fin N) r).card →
      let H := extensionState ω.1 ω.2 j
      let X := cycleCount r original H (originalPorts original)
      0 < X → logarithmicBaseline r (ordinaryEdgeCount r original) j original -
        (N:ℝ)/Real.sqrt (Real.log N) ≤ Real.log (X:ℝ) →
      ∀ (b : Base original) (S q : Finset ↥(active b)) (x : ↥(active b)),
      S.card = r-3 →
      LegalPrivateCompletion r (restrictEdges (active b) (markers hadm.marker_matching b))
        (insert x S) q →
      (X:ℝ)/(N:ℝ)^(3*r) ≤ sourceCount r hadm.marker_matching b H S q x →
      Mobility (r := r) hadm.marker_matching b H S q x c := by
  have hrp : (0:ℝ) < r := by exact_mod_cast (show 0 < r by omega)
  have ha : (0:ℝ) < 1/(2*(r:ℝ)) := by positivity
  filter_upwards [BootstrapPrivateMobilityScales.eventually_private_mobility_bounds r hr,
    BootstrapPrivateCommonEvent.eventually_source_candidates r hr (1/(2*(r:ℝ))) ha,
    eventually_terminal_mean_lower, BootstrapTagFrames.eventually_admissible_tag_room]
    with N hsc hcan hmean hroom
  intro m ell original offset hadm
  have hroom' : 2*original.card+2 ≤ Fintype.card (Fin N) := by
    simpa using hroom r m ell original offset hadm
  refine ⟨hroom',?_⟩
  intro h hR cE cPort c C L hc ω hω j hj hK H X hX hAX b S q x hS hs hlarge
  have hNp : 0 < N := by have := hsc.1; omega
  have hm : Real.log (Fintype.card (Fin N) : ℝ)/2 ≤ meanDegree (V := Fin N) r m := by
    simpa using hmean r m ell original offset hadm
  have hcard := extensionState_card ω.1 ω.2 j hj hK
  have hlow := BootstrapPrivateAdmissibleParameters.later_time_lower hr
    (by simpa using hNp : 0 < Fintype.card (Fin N)) hj hm
  have hW := BootstrapPrivateAdmissibleParameters.positive_source_of_large hNp hX hlarge
  obtain ⟨F,hd,hmarkers,hrel⟩ := BootstrapPrivateAdmissibleParameters.exists_source
    hadm.marker_matching b hr S q x hs
  have hpow : (X:ℝ)*(N:ℝ)^(-(3*(r:ℝ))) ≤ sourceCount r hadm.marker_matching b H S q x := by
    rw [show (3*(r:ℝ)) = ((3*r:ℕ):ℝ) by push_cast; ring,
      Real.rpow_neg (Nat.cast_nonneg N), Real.rpow_natCast]
    simpa only [div_eq_mul_inv] using hlarge
  have hbalance := hcan (ordinaryEdgeCount r original) original
    (by simpa using hadm.vertex_bookkeeping) hadm.marker_matching hadm.markers_nonempty
    (by simpa using hadm.markers_small) m h hR ell c C L (rootConstant c) _ ω hω j hj hK
    (by simpa only [hcard,Fintype.card_fin] using hlow) X hX
    (by simpa only [hcard] using hAX) b F S q x hd hmarkers hrel hpow
  have hbounds := hsc.2.2.2.2 original.card (by simpa using hadm.markers_small)
  exact of_candidates hadm.marker_matching hr hroom' cE cPort c C L hc.le ω hω hm j hj hK
    b S q x hS hs F hd hmarkers hrel hW hbalance hsc.1 hsc.2.1 hsc.2.2.1
    hbounds.1 hbounds.2

end LooseHamilton.BootstrapPrivateMobility
