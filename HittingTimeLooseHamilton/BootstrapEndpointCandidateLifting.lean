module

public import HittingTimeLooseHamilton.BootstrapPrivateCandidateLifting
public import HittingTimeLooseHamilton.BootstrapEndpointMatching
public import HittingTimeLooseHamilton.CycleOnCounting

public section

/-! Endpoint splice candidates retain the original forbidden ports on either base. -/
noncomputable section
namespace LooseHamilton.BootstrapEndpointCandidateLifting
open Finset BootstrapBases
variable {V : Type} [Fintype V] [DecidableEq V]
variable {r : ℕ} {M : Finset (Finset V)}

/-- Generic ambient transport for the actual cut marker family, including erasure. -/
theorem candidate_of_geometry (b : Base M) (F : AuxiliaryFrame.Frame r M)
    (D Q : Finset ↥(active b)) (K : Finset (Finset ↥(active b)))
    (u v : ↥(active b))
    (hd : F.val.deleted = deleted b ∪ liftEdge (active b) D)
    (hm : F.markers = K.image (liftEdge (active b)))
    (hc : LegalPrivateCompletion r K Q {u,v})
    (hs : Q ∪ {u,v} ⊆ univ \ D)
    (ha : Q ∪ {u,v} ∈ allowedEdges r (fixedPorts b)) :
    F.LegalCandidate (liftEdge (active b) Q, u.val, v.val) := by
  have hc' : LegalPrivateCompletion r (restrictEdges (active b) F.markers) Q {u,v} := by
    simpa only [hm, restrictEdges_liftEdges] using hc
  refine ⟨?_, ?_, ?_⟩
  · simpa only [liftEdge_pair] using hc'.lift
  · change liftEdge (active b) Q ∪ {u.val,v.val} ⊆ univ \ F.val.deleted
    rw [hd, ← liftEdge_pair, ← liftEdge_union]
    intro w hw
    obtain ⟨a, ha, rfl⟩ := mem_image.mp hw
    refine mem_sdiff.mpr ⟨mem_univ _, ?_⟩
    intro hx
    rcases mem_union.mp hx with hD | hP
    · exact (mem_sdiff.mp a.property).2 hD
    · have hap : a ∈ restrictEdge (active b) (liftEdge (active b) D) :=
        (mem_restrictEdge _ _ a).mpr hP
      exact (mem_sdiff.mp (hs ha)).2 (by simpa only [restrict_liftEdge] using hap)
  · rw [← liftEdge_pair, ← liftEdge_union]
    exact (liftEdge_mem_allowed_iff r (active b) (originalPorts M) _).mpr ha


/-- Removing the exposed endpoint and inserting the target yields an allowed
candidate; its forbidden ports are the fixed original ones. -/
theorem splice_geometry {W : Type} [Fintype W] [DecidableEq W]
    {r : ℕ} (hr : 3 ≤ r) {K R G : Finset (Finset W)}
    {P D Q U : Finset W} {y z a t v : W} (hK : K ⊆ R)
    (h : EndpointSpliceLegal r R G P D y z a t Q v)
    (he : {y,v} ∪ Q ∈ allowedEdges r U) (ht : t ∉ U) :
    LegalPrivateCompletion r (insert {a,z} K) Q {v,t} ∧
      Q ∪ {v,t} ⊆ univ \ (P ∪ D) ∧ Q ∪ {v,t} ∈ allowedEdges r U := by
  have hc := endpointSpliceLegal_privateCompletion hK h
  refine ⟨hc, ?_, ?_⟩
  · intro w hw
    refine mem_sdiff.mpr ⟨mem_univ _, ?_⟩
    intro hdel
    rcases mem_union.mp hw with hw | hw
    · exact disjoint_left.mp h.private_disjoint hw (by
        simp only [mem_union] at hdel ⊢; tauto)
    · simp only [mem_insert, mem_singleton] at hw
      rcases hw with rfl | rfl
      · exact h.newEndpoint_fresh (mem_union_left _ (mem_union_left _ hdel))
      · exact h.target_fresh (mem_union_left _ (mem_union_left _ hdel))
  · apply (mem_allowedEdges _ _ _).mpr
    refine ⟨?_, ?_⟩
    · rw [card_union_of_disjoint hc.private_pair_disjoint, hc.private_card, hc.pair_card]
      omega
    · have hsub : (Q ∪ {v,t}) ∩ U ⊆ ({y,v} ∪ Q) ∩ U := by
        intro w hw
        obtain ⟨hw,hU⟩ := mem_inter.mp hw
        refine mem_inter.mpr ⟨?_,hU⟩
        rcases mem_union.mp hw with hQ | hp
        · exact mem_union_right _ hQ
        · simp only [mem_insert, mem_singleton] at hp
          rcases hp with rfl | rfl
          · simp
          · exact (ht hU).elim
      exact (card_le_card hsub).trans ((mem_allowedEdges _ _ _).mp he).2

/-- A residual Type I splice is a legal candidate of the actual ambient core. -/
theorem candidate_I (hM : IsPairMatching M) (b : Base M)
    (F : AuxiliaryFrame.Frame r M) (hr : 3 ≤ r)
    (G : SimpleHypergraph ↥(active b)) (P : Finset ↥(active b))
    (y z t : ↥(active b)) (l : EndpointCutLabelI ↥(active b))
    (q : EndpointSpliceInnerLabel ↥(active b))
    (hd : F.val.deleted = deleted b ∪ liftEdge (active b) (P ∪ l.deleted y))
    (hm : F.markers = (l.markers (restrictEdges (active b) (markers hM b)) z).image
      (liftEdge (active b)))
    (h : EndpointSpliceLegalI r (restrictEdges (active b) (markers hM b)) G P y z t l q)
    (he : {y,q.2} ∪ q.1 ∈ allowedEdges r (fixedPorts b)) (ht : t ∉ fixedPorts b) :
    F.LegalCandidate (liftEdge (active b) q.1,q.2.val,t.val) := by
  obtain ⟨hc,hs,ha⟩ := splice_geometry hr (Subset.refl _) h he ht
  exact candidate_of_geometry b F _ _ _ _ _ hd hm hc hs ha

/-- Type II uses the erased cut marker, with the same two prescribed starts. -/
theorem candidate_II (hM : IsPairMatching M) (b : Base M)
    (F : AuxiliaryFrame.Frame r M) (hr : 3 ≤ r)
    (G : SimpleHypergraph ↥(active b)) (P : Finset ↥(active b))
    (y z t : ↥(active b)) (l : EndpointCutLabelII ↥(active b))
    (q : EndpointSpliceInnerLabel ↥(active b))
    (hd : F.val.deleted = deleted b ∪ liftEdge (active b) (P ∪ l.deleted y))
    (hm : F.markers = (l.markers (restrictEdges (active b) (markers hM b)) z).image
      (liftEdge (active b)))
    (h : EndpointSpliceLegalII r (restrictEdges (active b) (markers hM b)) G P y z t l q)
    (he : {y,q.2} ∪ q.1 ∈ allowedEdges r (fixedPorts b)) (ht : t ∉ fixedPorts b) :
    F.LegalCandidate (liftEdge (active b) q.1,q.2.val,t.val) := by
  obtain ⟨hc,hs,ha⟩ := splice_geometry hr (erase_subset _ _) h he ht
  exact candidate_of_geometry b F _ _ _ _ _ hd hm hc hs ha

end LooseHamilton.BootstrapEndpointCandidateLifting
