module

public import HittingTimeLooseHamilton.BootstrapPrivateCommonEvent
public import HittingTimeLooseHamilton.BootstrapEndpointLiftedBadSet
public import HittingTimeLooseHamilton.EndpointRootEventMobility

public section

/-! The literal endpoint test is a member of the fixed ambient registry. -/
noncomputable section
namespace LooseHamilton.BootstrapEndpointRegistryCoverage
open Finset BootstrapBases BootstrapCatalogue RootFreeTestIndexing
variable {V : Type} [Fintype V] [DecidableEq V]
variable {r : ℕ} {original : Finset (Finset V)}

@[expose] def endpointBaseLabel (hM : IsPairMatching original) (b : Base original)
    (G : SimpleHypergraph ↥(active b)) (P : Finset ↥(active b))
    (hP : P.card = r-2) (y z t : ↥(active b))
    (l : EndpointMigrationCut r (restrictEdges (active b) (markers hM b)) G P y z) : BaseLabel r V := by
  cases l with
  | inl l =>
    have hl := (mem_endpointCutLabelsI _ _ _ _ _ _ _).mp l.property
    exact .inr (.inl (endpointLabelI r (liftEdge (active b) P) (by simpa using hP)
      y.val z.val t.val (l.val.1.val,liftEdge (active b) l.val.2)
      (by simpa using hl.private_card)))
  | inr l =>
    have hl := (mem_endpointCutLabelsII _ _ _ _ _ _ _).mp l.property
    exact .inr (.inr (endpointLabelII r (liftEdge (active b) P) (by simpa using hP)
      y.val z.val t.val (l.val.1.val,l.val.2.1.val,l.val.2.2.1.val,
        liftEdge (active b) l.val.2.2.2.1,liftEdge (active b) l.val.2.2.2.2)
      (by simpa using hl.first_private_card) (by simpa using hl.second_private_card)))

theorem endpointBaseLabel_admissible (hM : IsPairMatching original) (b : Base original)
    (G : SimpleHypergraph ↥(active b)) (P : Finset ↥(active b))
    (hP : P.card = r-2) (y z t : ↥(active b))
    (hs : LegalPrivateCompletion r (restrictEdges (active b) (markers hM b)) P {y,z})
    (l : EndpointMigrationCut r (restrictEdges (active b) (markers hM b)) G P y z) :
    admissible (.inl (b,endpointBaseLabel hM b G P hP y z t l)) := by
  have hyz : y ≠ z := by intro he; subst z; simpa using hs.pair_card
  have hdis : Disjoint (liftEdge (active b) P) {y.val,z.val} := by
    rw [← liftEdge_pair]
    exact (disjoint_image Subtype.val_injective).mpr hs.private_pair_disjoint
  cases l with
  | inl l =>
    constructor
    · change liftEdge (active b) P ∪ liftEdge (active b) l.val.2 ∪
        {y.val,z.val,t.val,l.val.1.val} ⊆ active b
      apply union_subset (union_subset (liftEdge_subset _ _) (liftEdge_subset _ _))
      intro a ha
      simp only [mem_insert,mem_singleton] at ha
      rcases ha with rfl | rfl | rfl | rfl
      · exact y.property
      · exact z.property
      · exact t.property
      · exact l.val.1.property
    · exact ⟨fun he => hyz (Subtype.ext he),hdis⟩
  | inr l =>
    constructor
    · change liftEdge (active b) P ∪ liftEdge (active b) l.val.2.2.2.1 ∪
        liftEdge (active b) l.val.2.2.2.2 ∪ {y.val,z.val,t.val,l.val.1.val,l.val.2.1.val,l.val.2.2.1.val} ⊆ active b
      apply union_subset (union_subset (union_subset (liftEdge_subset _ _) (liftEdge_subset _ _)) (liftEdge_subset _ _))
      intro a ha
      simp only [mem_insert,mem_singleton] at ha
      rcases ha with rfl | rfl | rfl | rfl | rfl | rfl
      · exact y.property
      · exact z.property
      · exact t.property
      · exact l.val.1.property
      · exact l.val.2.1.property
      · exact l.val.2.2.1.property
    · exact ⟨fun he => hyz (Subtype.ext he),hdis⟩

theorem endpoint_test_eq (hM : IsPairMatching original) (b : Base original)
    (G : SimpleHypergraph ↥(active b)) (P : Finset ↥(active b))
    (hP : P.card = r-2) (y z t : ↥(active b))
    (hs : LegalPrivateCompletion r (restrictEdges (active b) (markers hM b)) P {y,z})
    (l : EndpointMigrationCut r (restrictEdges (active b) (markers hM b)) G P y z)
    (h : ℕ) (cP cE cPort : ℝ) (j : Fin ((Fintype.card V)^r+1)) :
    tests (h := h) hM cP cE cPort (baseIndex b (endpointBaseLabel hM b G P hP y z t l) j) =
      (registerEndpointRootTest r h j.val (restrictEdges (active b) (markers hM b))
        P (fixedPorts b) y z t (endpointMigrationRawLabel l) cE ∅
        (empty_subset _) (by simp)).liftDeleted (deleted b) := by
  rw [tests_base _ _ _ _ _ _ _ (endpointBaseLabel_admissible hM b G P hP y z t hs l)]
  cases l <;> simp only [endpointBaseLabel,endpointLabelI,endpointLabelII,residualTest,
    block_val,residualMarkers,endpointMigrationRawLabel,restrict_liftEdge]

theorem endpoint_nonfailure {N m h hR : ℕ} {ell : Fin N → ℕ}
    {original : Finset (Finset (Fin N))} (hM : IsPairMatching original) (hr : 3 ≤ r)
    (hroom : 2*original.card+2 ≤ Fintype.card (Fin N))
    (cP cPort c C L : ℝ) (hc : 0 ≤ c)
    (ω : CandidateBalance.Outcome (Fin N) r m ell)
    (hω : RootFreeCommonEvent
      (fixedRegistry (h := hR) hM hr hroom cP (BootstrapConstants.rootThreshold r) cPort)
      h c C L 2 (rootConstant c) ω)
    (hmean : Real.log (Fintype.card (Fin N) : ℝ)/2 ≤ meanDegree (V := Fin N) r m)
    (b : Base original) (G : SimpleHypergraph ↥(active b)) (P : Finset ↥(active b))
    (hP : P.card = r-2) (y z t : ↥(active b))
    (hs : LegalPrivateCompletion r (restrictEdges (active b) (markers hM b)) P {y,z})
    (l : EndpointMigrationCut r (restrictEdges (active b) (markers hM b)) G P y z)
    (j : Fin ((Fintype.card (Fin N))^r+1)) (hj : m ≤ j.val)
    (hK : j.val ≤ (completeEdges (Fin N) r).card)
    (hdensity : rootLinkDensity r y.val
      (BootstrapEndpointLiftedBadSet.registeredBadSet r hR j.val hM b P y z t
        (endpointMigrationRawLabel l)
        (rootFreePairObservation r m ell j.val y.val ω).1
        (rootFreePairObservation r m ell j.val y.val ω).2) ≤
      FrameScales.rho (Fintype.card (Fin N))) :
    ¬ RootLinkBad
      (BootstrapEndpointLiftedBadSet.registeredBadSet r hR j.val hM b P y z t
        (endpointMigrationRawLabel l)
        (rootFreePairObservation r m ell j.val y.val ω).1
        (rootFreePairObservation r m ell j.val y.val ω).2)
      (j.val-(rootFreePairObservation r m ell j.val y.val ω).2.card)
      (rootSamplingPair r m ell j.val ω) := by
  have he := endpoint_test_eq hM b G P hP y z t hs l hR
    cP (BootstrapConstants.rootThreshold r) cPort j
  have hh := BootstrapPrivateCommonEvent.catalogue_nonfailure hM hr hroom cP
    (BootstrapConstants.rootThreshold r) cPort c C L hc ω hω hmean
    (baseIndex b (endpointBaseLabel hM b G P hP y z t l) j) hj hK
  rw [he] at hh
  exact hh hdensity

theorem endpoint_nonfailure_actual {N m h hR : ℕ} {ell : Fin N → ℕ}
    {original : Finset (Finset (Fin N))} (hM : IsPairMatching original) (hr : 3 ≤ r)
    (hroom : 2*original.card+2 ≤ Fintype.card (Fin N))
    (cP cPort c C L : ℝ) (hc : 0 ≤ c)
    (ω : CandidateBalance.Outcome (Fin N) r m ell)
    (hω : RootFreeCommonEvent
      (fixedRegistry (h := hR) hM hr hroom cP (BootstrapConstants.rootThreshold r) cPort)
      h c C L 2 (rootConstant c) ω)
    (hmean : Real.log (Fintype.card (Fin N) : ℝ)/2 ≤ meanDegree (V := Fin N) r m)
    (b : Base original) (G : SimpleHypergraph ↥(active b)) (P : Finset ↥(active b))
    (hP : P.card = r-2) (y z t : ↥(active b))
    (hs : LegalPrivateCompletion r (restrictEdges (active b) (markers hM b)) P {y,z})
    (l : EndpointMigrationCut r (restrictEdges (active b) (markers hM b)) G P y z)
    (j : Fin ((Fintype.card (Fin N))^r+1)) (hj : m ≤ j.val)
    (hK : j.val ≤ (completeEdges (Fin N) r).card)
    (hdensity : rootLinkDensity r y.val
      (BootstrapEndpointLiftedBadSet.registeredBadSet r hR j.val hM b P y z t
        (endpointMigrationRawLabel l)
        (rootFreePairObservation r m ell j.val y.val ω).1
        (rootFreePairObservation r m ell j.val y.val ω).2) ≤
      FrameScales.rho (Fintype.card (Fin N))) :
    ¬ RootLinkBad
      (BootstrapEndpointLiftedBadSet.registeredBadSet r hR j.val hM b P y z t
        (endpointMigrationRawLabel l) ω.1.val (extensionState ω.1 ω.2 j.val))
      (vertexDegree (extensionState ω.1 ω.2 j.val) y.val)
      (ω.1.val,extensionState ω.1 ω.2 j.val) := by
  have hh := endpoint_nonfailure hM hr hroom cP cPort c C L hc ω hω hmean
    b G P hP y z t hs l j hj hK hdensity
  rw [sampling_degree_eq ω hj hK y.val] at hh
  change ¬ RootLinkBad
    (BootstrapEndpointLiftedBadSet.registeredBadSet r hR j.val hM b P y z t
      (endpointMigrationRawLabel l) (rootFreeEdges y.val ω.1.val)
      (rootFreeEdges y.val (extensionState ω.1 ω.2 j.val)))
    (vertexDegree (extensionState ω.1 ω.2 j.val) y.val)
    (ω.1.val,extensionState ω.1 ω.2 j.val) at hh
  rw [BootstrapEndpointLiftedBadSet.observation_eq] at hh
  exact hh

end LooseHamilton.BootstrapEndpointRegistryCoverage
