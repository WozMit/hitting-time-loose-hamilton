module

public import HittingTimeLooseHamilton.BootstrapActualBudgets
public import HittingTimeLooseHamilton.BootstrapPrivateSourceNormalization
public import HittingTimeLooseHamilton.BootstrapSamplingGates
public import HittingTimeLooseHamilton.BootstrapActualCoverage

public section

/-! Item 33.15.8: budgets and sampling gates are conclusions on the fixed
common event. The source cutoff uses the manuscript exponent `3*r`. -/
noncomputable section
namespace LooseHamilton.BootstrapPrivateCommonEvent
open Finset Filter BootstrapBases BootstrapCatalogue

 theorem source_cutoff {N r X W : ℕ} (hN : 1 ≤ N)
    (hW : (X : ℝ)*(N : ℝ)^(-(3*(r : ℝ))) ≤ W) :
    (X : ℝ)*(N : ℝ)^(-(100*(r : ℝ))) ≤ W := by
  have he : -(100*(r:ℝ)) ≤ -(3*(r:ℝ)) := by nlinarith [show (0:ℝ) ≤ r from Nat.cast_nonneg r]
  exact (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN : (1:ℝ) ≤ N) he)
    (Nat.cast_nonneg X)).trans hW

 theorem eventually_source_candidates (r : ℕ) (hr : 3 ≤ r) (c : ℝ) (hc : 0 < c) :
    ∀ᶠ N : ℕ in atTop, ∀ k : ℕ, ∀ original : Finset (Finset (Fin N)),
      N = (r-1)*k+original.card → ∀ hM : IsPairMatching original,
      1 ≤ original.card → (original.card : ℝ) ≤ (N : ℝ)^(1/10 : ℝ) →
      ∀ m h hR : ℕ, ∀ ell : Fin N → ℕ, ∀ cEvent C L cRoot : ℝ,
      ∀ tests : RootFreeTestIndexing.RootTestIndex r original → RegisteredRootTest (Fin N) r hR,
      ∀ ω : CandidateBalance.Outcome (Fin N) r m ell,
      RootFreeCommonEvent tests h cEvent C L 2 cRoot ω →
      ∀ j : ℕ, m ≤ j → j ≤ (completeEdges (Fin N) r).card →
      c*N*Real.log N ≤ (extensionState ω.1 ω.2 j).card →
      ∀ X : ℕ, 0 < X → logarithmicBaseline r k (extensionState ω.1 ω.2 j).card original -
        (N : ℝ)/Real.sqrt (Real.log N) ≤ Real.log (X : ℝ) →
      ∀ b : Base original, ∀ F : AuxiliaryFrame.Frame r original,
      ∀ S q : Finset ↥(active b), ∀ x : ↥(active b),
      F.val.deleted = deleted b ∪ liftEdge (active b) (insert x S) →
      F.markers = insert (liftEdge (active b) q) (markers hM b) →
      F.val.relative = none →
      (X : ℝ)*(N : ℝ)^(-(3*(r : ℝ))) ≤
        completionCount r (restrictEdges (active b) (markers hM b))
          (fixedPortHost (inducedHost (active b) (extensionState ω.1 ω.2 j)) (fixedPorts b))
          (insert x S) q →
      ¬ F.candidateBad (extensionState ω.1 ω.2 j) (FrameScales.alpha N) := by
  filter_upwards [BootstrapActualBudgets.eventually_all_frames r hr c hc,
    eventually_ge_atTop 1] with N hb hN
  intro k original hsize hM hs hsbound m h hR ell cEvent C L cRoot tests ω hω j hj hK hlow
    X hX hAX b F S q x hd hm hrel hW
  have hH := extensionState_subset ω.1 ω.2 j
  have hcard : (extensionState ω.1 ω.2 j).card ≤ N.choose r := by
    simpa only [completeEdges_card, Fintype.card_fin] using card_le_card hH
  have hbudget := hb k original hsize hM hs hsbound _ hlow hcard X hX hAX F
  have hw := source_cutoff hN hW
  rw [← BootstrapPrivateSourceNormalization.frame_source_count hM b F _ hH S q x hd hm hrel] at hw
  have hh := hω.candidates F j hj hK (hbudget hw)
  simpa only [AuxiliaryFrame.Frame.candidateBadAtScale,Fintype.card_fin] using hh

 theorem catalogue_nonfailure {N r m h hR : ℕ} {ell : Fin N → ℕ}
    {original : Finset (Finset (Fin N))} (hM : IsPairMatching original) (hr : 3 ≤ r)
    (hroom : 2*original.card+2 ≤ Fintype.card (Fin N))
    (cP cE cPort c C L : ℝ) (hc : 0 ≤ c)
    (ω : CandidateBalance.Outcome (Fin N) r m ell)
    (hω : RootFreeCommonEvent (fixedRegistry (h := hR) hM hr hroom cP cE cPort)
      h c C L 2 (rootConstant c) ω)
    (hmean : Real.log (Fintype.card (Fin N) : ℝ)/2 ≤ meanDegree (V := Fin N) r m)
    (i : Index r original) (hj : m ≤ i.2.val)
    (hK : i.2.val ≤ (completeEdges (Fin N) r).card)
    (hdensity : rootLinkDensity r (tests (h := hR) hM cP cE cPort i).root
      ((tests (h := hR) hM cP cE cPort i).badSet
        (rootFreePairObservation r m ell i.2.val (tests (h := hR) hM cP cE cPort i).root ω)) ≤
      FrameScales.rho (Fintype.card (Fin N))) :
    ¬ RootLinkBad
      ((tests (h := hR) hM cP cE cPort i).badSet
        (rootFreePairObservation r m ell i.2.val (tests (h := hR) hM cP cE cPort i).root ω))
      (i.2.val-(rootFreePairObservation r m ell i.2.val (tests (h := hR) hM cP cE cPort i).root ω).2.card)
      (rootSamplingPair r m ell i.2.val ω) := by
  have hp := hω.root_test (catalogueEmbedding hM hr hroom i)
  simp only [fixedRegistry_entry, tests_time] at hp
  apply hp hj hK (prescribed_present hM cP cE cPort i ω) _ hdensity
  exact sampling_degree_lower ω hj hK hc hmean (hω.1.2.1 _ hj hK) _

end LooseHamilton.BootstrapPrivateCommonEvent
