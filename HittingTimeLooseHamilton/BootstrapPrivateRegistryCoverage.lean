module

public import HittingTimeLooseHamilton.BootstrapPrivateCommonEvent
public import HittingTimeLooseHamilton.BootstrapPrivateLiftedBadSet

public section

/-! Literal coverage of a residual private test by the fixed ambient registry. -/
noncomputable section
namespace LooseHamilton.BootstrapPrivateCommonEvent
open Finset BootstrapBases BootstrapCatalogue RootFreeTestIndexing
variable {V : Type} [Fintype V] [DecidableEq V]
variable {r : ℕ} {original : Finset (Finset V)}

@[expose] def privateBaseLabel (b : Base original) (S : Finset ↥(active b))
    (hS : S.card = r-3) (x y z t : ↥(active b)) : BaseLabel r V :=
  .inl (privateLabel r (liftEdge (active b) S) (by rw [liftEdge_card,hS]) x.val y.val z.val t.val)

theorem privateBaseLabel_admissible (hM : IsPairMatching original) (hr : 3 ≤ r)
    (b : Base original) (S : Finset ↥(active b)) (hS : S.card = r-3)
    (x y z t : ↥(active b))
    (hs : LegalPrivateCompletion r (restrictEdges (active b) (markers hM b)) (insert x S) {y,z}) :
    admissible (.inl (b,privateBaseLabel b S hS x y z t)) := by
  have hx : x ∉ S := by
    intro hx
    have hh := hs.private_card
    rw [insert_eq_of_mem hx,hS] at hh
    omega
  have hxy : x ≠ y := by
    intro he; subst y
    exact disjoint_left.mp hs.private_pair_disjoint (mem_insert_self _ _) (by simp)
  have hxz : x ≠ z := by
    intro he; subst z
    exact disjoint_left.mp hs.private_pair_disjoint (mem_insert_self _ _) (by simp)
  have hyz : y ≠ z := by
    intro he; subst z
    simpa using hs.pair_card
  constructor
  · change liftEdge (active b) S ∪ {x.val,y.val,z.val,t.val} ⊆ active b
    apply union_subset (liftEdge_subset _ _)
    intro a ha
    simp only [mem_insert,mem_singleton] at ha
    rcases ha with rfl | rfl | rfl | rfl
    · exact x.property
    · exact y.property
    · exact z.property
    · exact t.property
  · change x.val ≠ y.val ∧ x.val ≠ z.val ∧ y.val ≠ z.val ∧
      Disjoint (liftEdge (active b) S) {x.val,y.val,z.val}
    refine ⟨fun h => hxy (Subtype.ext h),fun h => hxz (Subtype.ext h),
      fun h => hyz (Subtype.ext h),?_⟩
    apply disjoint_left.mpr
    intro a ha hb
    change a ∈ S.image Subtype.val at ha
    obtain ⟨v,hv,hev⟩ := mem_image.mp ha
    subst a
    simp only [mem_insert,mem_singleton] at hb
    rcases hb with he | he | he
    · exact hx (by simpa only [Subtype.ext he] using hv)
    · exact disjoint_left.mp hs.private_pair_disjoint (mem_insert_of_mem hv)
        (by simpa only [Subtype.ext he] using (show y ∈ ({y,z}:Finset _) by simp))
    · exact disjoint_left.mp hs.private_pair_disjoint (mem_insert_of_mem hv)
        (by simpa only [Subtype.ext he] using (show z ∈ ({y,z}:Finset _) by simp))

theorem private_test_eq (hM : IsPairMatching original) (hr : 3 ≤ r)
    (b : Base original) (S : Finset ↥(active b)) (hS : S.card = r-3)
    (x y z t : ↥(active b))
    (hs : LegalPrivateCompletion r (restrictEdges (active b) (markers hM b)) (insert x S) {y,z})
    (h : ℕ) (cP cE cPort : ℝ) (j : Fin ((Fintype.card V)^r+1)) :
    tests (h := h) hM cP cE cPort (baseIndex b (privateBaseLabel b S hS x y z t) j) =
      (registerPrivateRootTest r h j.val (restrictEdges (active b) (markers hM b))
        S {y,z} (fixedPorts b) x t cP).liftDeleted (deleted b) := by
  rw [tests_base _ _ _ _ _ _ _ (privateBaseLabel_admissible hM hr b S hS x y z t hs)]
  simp only [residualTest,privateBaseLabel,privateLabel,block_val,residualMarkers]
  rw [restrict_liftEdge]

 theorem private_nonfailure {N m h hR : ℕ} {ell : Fin N → ℕ}
    {original : Finset (Finset (Fin N))} (hM : IsPairMatching original) (hr : 3 ≤ r)
    (hroom : 2*original.card+2 ≤ Fintype.card (Fin N))
    (cE cPort c C L : ℝ) (hc : 0 ≤ c)
    (ω : CandidateBalance.Outcome (Fin N) r m ell)
    (hω : RootFreeCommonEvent
      (fixedRegistry (h := hR) hM hr hroom (BootstrapConstants.rootThreshold r) cE cPort)
      h c C L 2 (rootConstant c) ω)
    (hmean : Real.log (Fintype.card (Fin N) : ℝ)/2 ≤ meanDegree (V := Fin N) r m)
    (b : Base original) (S : Finset ↥(active b)) (hS : S.card = r-3)
    (x y z t : ↥(active b))
    (hs : LegalPrivateCompletion r (restrictEdges (active b) (markers hM b)) (insert x S) {y,z})
    (j : Fin ((Fintype.card (Fin N))^r+1)) (hj : m ≤ j.val)
    (hK : j.val ≤ (completeEdges (Fin N) r).card)
    (hdensity : rootLinkDensity r x.val
      (BootstrapPrivateLiftedBadSet.registeredBadSet r hR j.val hM b S {y,z} x t
        (rootFreePairObservation r m ell j.val x.val ω).1
        (rootFreePairObservation r m ell j.val x.val ω).2) ≤
      FrameScales.rho (Fintype.card (Fin N))) :
    ¬ RootLinkBad
      (BootstrapPrivateLiftedBadSet.registeredBadSet r hR j.val hM b S {y,z} x t
        (rootFreePairObservation r m ell j.val x.val ω).1
        (rootFreePairObservation r m ell j.val x.val ω).2)
      (j.val-(rootFreePairObservation r m ell j.val x.val ω).2.card)
      (rootSamplingPair r m ell j.val ω) := by
  have he := private_test_eq hM hr b S hS x y z t hs hR
    (BootstrapConstants.rootThreshold r) cE cPort j
  have hh := catalogue_nonfailure hM hr hroom (BootstrapConstants.rootThreshold r)
    cE cPort c C L hc ω hω hmean (baseIndex b (privateBaseLabel b S hS x y z t) j) hj hK
  rw [he] at hh
  exact hh hdensity

end LooseHamilton.BootstrapPrivateCommonEvent
