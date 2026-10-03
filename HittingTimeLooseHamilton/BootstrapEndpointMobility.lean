module

public import HittingTimeLooseHamilton.BootstrapEndpointCutContributions
public import HittingTimeLooseHamilton.BootstrapEndpointWeightedAveraging
public import HittingTimeLooseHamilton.BootstrapEndpointMobilityScales

public section

noncomputable section
namespace LooseHamilton.BootstrapEndpointMobility
open Finset Filter BootstrapBases BootstrapCatalogue

/-- Passing from a large source to every retained cut preserves the polynomial
cut floor used by the registered endpoint implication. -/
theorem retained_large {N r : ℕ} {X W w : ℝ}
    (hsource : X/(N:ℝ)^(3*r) ≤ W)
    (hretained : W/(N:ℝ)^(2*r+2) ≤ w) :
    X/(N:ℝ)^(5*r+2) ≤ w := by
  have hh := div_le_div_of_nonneg_right hsource
    (pow_nonneg (Nat.cast_nonneg N) (2*r+2))
  rw [div_div, ← pow_add] at hh
  have he : 3*r+(2*r+2)=5*r+2 := by omega
  rw [he] at hh
  exact hh.trans hretained

/-- The ambient exceptional set is uniformly small; the source and target
counts are the literal fixed-port completion counts on either residual base. -/
@[expose] def Mobility {N r : ℕ} {original : Finset (Finset (Fin N))}
    (hM : IsPairMatching original) (b : Base original) (H : SimpleHypergraph (Fin N))
    (P : Finset ↥(active b)) (y z : ↥(active b)) (c : ℝ) : Prop :=
  ∃ E : Finset (Fin N),
    (E.card:ℝ) ≤ Real.sqrt 2*(FrameScales.alpha N)^(1/4:ℝ)*N ∧
    ∀ t : ↥(active b), t.val ∉ E →
      BootstrapConstants.endpointFactor r c *
        (completionCount r (restrictEdges (active b) (markers hM b))
          (fixedPortHost (inducedHost (active b) H) (fixedPorts b)) P {y,z}:ℝ) ≤
        completionCount r (restrictEdges (active b) (markers hM b))
          (fixedPortHost (inducedHost (active b) H) (fixedPorts b)) P {t,z}

/-- Endpoint mobility for every legal large source with the required fixed-port
geometry, on either base. All sampling, density and cut averaging hypotheses
are derived on the common event. -/
theorem eventually_endpoint_mobility (r : ℕ) (hr : 3 ≤ r) :
    ∀ᶠ N : ℕ in atTop, ∀ (m : ℕ) (ell : Fin N → ℕ)
      (original : Finset (Finset (Fin N))) (offset : ℝ)
      (hadm : CoreAdmissible r m ell original offset),
      ∃ hroom : 2*original.card+2 ≤ Fintype.card (Fin N),
      ∀ (h hR : ℕ) (cP cPort c C L : ℝ), 0 < c →
      ∀ (ω : CandidateBalance.Outcome (Fin N) r m ell),
      RootFreeCommonEvent
        (fixedRegistry (h := hR) hadm.marker_matching hr hroom
          cP (BootstrapConstants.rootThreshold r) cPort)
        h c C L 2 (rootConstant c) ω →
      ∀ j : ℕ, m ≤ j → j ≤ (completeEdges (Fin N) r).card →
      let H := extensionState ω.1 ω.2 j
      let X := cycleCount r original H (originalPorts original)
      0 < X → logarithmicBaseline r (ordinaryEdgeCount r original) j original -
        (N:ℝ)/Real.sqrt (Real.log N) ≤ Real.log (X:ℝ) →
      ∀ (b : Base original) (P : Finset ↥(active b)) (y z : ↥(active b)),
      LegalPrivateCompletion r (restrictEdges (active b) (markers hadm.marker_matching b))
        P {y,z} →
      EndpointSourcePorts (fixedPorts b)
        (restrictEdges (active b) (markers hadm.marker_matching b)) y z →
      (X:ℝ)/(N:ℝ)^(3*r) ≤
        (completionCount r (restrictEdges (active b) (markers hadm.marker_matching b))
          (fixedPortHost (inducedHost (active b) H) (fixedPorts b)) P {y,z}:ℝ) →
      Mobility (r := r) hadm.marker_matching b H P y z c := by
  filter_upwards [BootstrapEndpointCutContributions.eventually_cut_contributions r hr,
    BootstrapEndpointMobilityScales.eventually_endpoint_mobility_bounds r hr,
    BootstrapEndpointMobilityScales.eventually_weighted_bounds r] with N hcuts hscale hw
  intro m ell original offset hadm
  obtain ⟨hroom,hcuts⟩ := hcuts m ell original offset hadm
  refine ⟨hroom,?_⟩
  intro h hR cP cPort c C L hc ω hω j hj hK H X hX hAX b P y z hs hports hlarge
  let ε := Real.sqrt (2*Real.sqrt (FrameScales.alpha N))
  have hε : 0 < ε := hw.1
  have hεsmall : ε ≤ 1/4 := hw.2.1
  have hδ : Migration.cutLoss r N ≤ 1/4 := hw.2.2 N (by omega)
  have hH := extensionState_subset ω.1 ω.2 j
  have hVN : Fintype.card ↥(active b) ≤ N := by
    simpa using (BootstrapEndpointCutParameters.base_card_bounds b).2
  have hM := (BootstrapEndpointCutParameters.residual_matching hadm.marker_matching b).2
  have hG := BootstrapEndpointCutParameters.filtered_subset_allowed r (active b) H hH (fixedPorts b)
  have hsize := BootstrapEndpointCutParameters.source_room b hr
    (by simpa using hscale.1) P hs.private_card
  have happ := BootstrapEndpointWeightedAveraging.endpoint_fixed_factor_of_cut_exceptions
    N hVN hr hs hM hports hG hsize (univ : Finset ↥(active b)) ε c hε hc hδ hεsmall
  have hce : ∀ k ∈ BootstrapEndpointWeightedAveraging.ambientRetainedCuts N r
      (restrictEdges (active b) (markers hadm.marker_matching b))
      (fixedPortHost (inducedHost (active b) H) (fixedPorts b)) P y z,
      ∃ E : Finset ↥(active b), (E.card:ℝ) ≤ ε^2*N ∧
        ∀ t ∈ (univ : Finset ↥(active b)), t ∉ E →
          BootstrapConstants.privateFactor r c * endpointMigrationWeight k ≤
            ∑ q ∈ endpointMigrationLabels t k, endpointMigrationY t k q := by
    intro k hk
    have hklarge := retained_large hlarge
      ((mem_filter.mp hk).2)
    obtain ⟨E,hE,hcontrib⟩ := hcuts h hR cP cPort c C L hc ω hω j hj hK
      hX hAX b P y z hs k hklarge
    refine ⟨univ.filter (fun t : ↥(active b) => t.val ∈ E), ?_, ?_⟩
    · have hcard : (univ.filter (fun t : ↥(active b) => t.val ∈ E)).card ≤ E.card := by
        apply card_le_card_of_injOn Subtype.val
        · intro t ht; exact (mem_filter.mp ht).2
        · intro t ht u hu he; exact Subtype.ext he
      have heps : ε^2 = 2*Real.sqrt (FrameScales.alpha N) :=
        Real.sq_sqrt (by positivity)
      rw [heps]
      exact (Nat.cast_le.mpr hcard).trans hE
    · intro t ht hte
      have htE : t.val ∉ E := by simpa only [mem_filter,mem_univ,true_and] using hte
      exact (hcontrib t htE).2
  obtain ⟨E,hsub,hcard,hfinal⟩ := happ hce
  refine ⟨E.map (Function.Embedding.subtype _), ?_, ?_⟩
  · rw [card_map]
    dsimp only [ε] at hcard
    rw [BootstrapEndpointMobilityScales.weighted_fraction_eq N hscale.2.1.le] at hcard
    exact hcard
  · intro t ht
    have htE : t ∉ E := by
      intro hte
      exact ht (mem_map.mpr ⟨t,hte,rfl⟩)
    exact hfinal t (mem_univ _) htE

end LooseHamilton.BootstrapEndpointMobility
