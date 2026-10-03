module

public import HittingTimeLooseHamilton.BootstrapPrivateMobility
public import HittingTimeLooseHamilton.BootstrapEndpointMobility

public section

/-! Both kinds of actual mobility and every prefix cutoff on one fixed event. -/
noncomputable section
namespace LooseHamilton.BootstrapSequentialInputs
open Finset Filter BootstrapBases BootstrapCatalogue BootstrapConstants

structure Inputs {N r : ℕ} {M : Finset (Finset (Fin N))}
    (hM : IsPairMatching M) (b : Base M) (H : SimpleHypergraph (Fin N))
    (X c : ℝ) : Prop where
  size_pos : 0 < N
  private_move : ∀ (S q : Finset ↥(active b)) (x : ↥(active b)),
    S.card = r-3 →
    LegalPrivateCompletion r (restrictEdges (active b) (markers hM b)) (insert x S) q →
    X/(N:ℝ)^(3*r) ≤ BootstrapPrivateMobility.sourceCount r hM b H S q x →
    BootstrapPrivateMobility.Mobility (r:=r) hM b H S q x c
  endpoint_move : ∀ (P : Finset ↥(active b)) (y z : ↥(active b)),
    LegalPrivateCompletion r (restrictEdges (active b) (markers hM b)) P {y,z} →
    EndpointSourcePorts (fixedPorts b) (restrictEdges (active b) (markers hM b)) y z →
    X/(N:ℝ)^(3*r) ≤ (completionCount r (restrictEdges (active b) (markers hM b))
      (fixedPortHost (inducedHost (active b) H) (fixedPorts b)) P {y,z}:ℝ) →
    BootstrapEndpointMobility.Mobility (r:=r) hM b H P y z c
  cutoffs : ∀ k : ℕ, k ≤ r → ∀ W : ℝ, X/(N:ℝ)^(2*r) ≤ W →
    X/(N:ℝ)^(3*r) ≤ (mobilityFloor r c)^k*W ∧
    X/(N:ℝ)^(5*r+2) ≤ ((mobilityFloor r c)^k*W)/(N:ℝ)^(2*r+2) ∧
    X*(N:ℝ)^(-(100*r:ℝ)) ≤ ((mobilityFloor r c)^k*W)/(N:ℝ)^(2*r+2)

/-- The threshold is uniform over all cores, outcomes, times, bases and sources.
Only the fixed regularity constant is chosen before the size threshold. -/
theorem eventually_inputs (r : ℕ) (hr : 3 ≤ r) (c : ℝ) (hc : 0 < c) :
    ∀ᶠ N : ℕ in atTop, ∀ (m : ℕ) (ell : Fin N → ℕ)
      (original : Finset (Finset (Fin N))) (offset : ℝ)
      (hadm : CoreAdmissible r m ell original offset),
      ∃ hroom : 2*original.card+2 ≤ Fintype.card (Fin N),
      ∀ (h hR : ℕ) (cPort C L : ℝ)
        (ω : CandidateBalance.Outcome (Fin N) r m ell),
      RootFreeCommonEvent
        (fixedRegistry (h:=hR) hadm.marker_matching hr hroom
          (rootThreshold r) (rootThreshold r) cPort)
        h c C L 2 (rootConstant c) ω →
      ∀ j : ℕ, m ≤ j → j ≤ (completeEdges (Fin N) r).card →
      let H := extensionState ω.1 ω.2 j
      let X := cycleCount r original H (originalPorts original)
      0 < X → logarithmicBaseline r (ordinaryEdgeCount r original) j original -
        (N:ℝ)/Real.sqrt (Real.log N) ≤ Real.log (X:ℝ) →
      ∀ b : Base original, Inputs (r:=r) hadm.marker_matching b H X c := by
  filter_upwards [BootstrapPrivateMobility.eventually_private_mobility r hr,
    BootstrapEndpointMobility.eventually_endpoint_mobility r hr,
    eventually_fixed_cutoffs hr hc] with N hp he hcut
  intro m ell original offset hadm
  obtain ⟨hroom,hp⟩ := hp m ell original offset hadm
  obtain ⟨hroom',he⟩ := he m ell original offset hadm
  refine ⟨hroom, ?_⟩
  intro h hR cPort C L ω hω j hj hK H X hX hAX b
  refine ⟨hcut.1, ?_, ?_, ?_⟩
  · exact hp h hR (rootThreshold r) cPort c C L hc ω hω j hj hK hX hAX b
  · exact he h hR (rootThreshold r) cPort c C L hc ω hω j hj hK hX hAX b
  · intro k hk W hW
    exact hcut.2 k hk X W (Nat.cast_nonneg _) hW

end LooseHamilton.BootstrapSequentialInputs
