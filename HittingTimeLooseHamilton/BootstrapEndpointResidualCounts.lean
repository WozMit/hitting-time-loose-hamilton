module

public import HittingTimeLooseHamilton.BootstrapBaseDirectedDictionary
public import HittingTimeLooseHamilton.BootstrapFilteredBaseHost
public import HittingTimeLooseHamilton.EndpointSplicing

public section

/-! Exact endpoint dictionaries on the ordinary or original-port base.  Both
prescribed starts of every splice count are retained. -/
noncomputable section
namespace LooseHamilton.BootstrapEndpointResidualCounts
open Finset BootstrapBases AuxiliaryFrame
variable {V : Type} [Fintype V] [DecidableEq V]
variable {r : ℕ} {M : Finset (Finset V)}

theorem core_count (b : Base M) (F : Frame r M) (H : SimpleHypergraph V)
    (hH : H ⊆ completeEdges V r) (D : Finset ↥(active b))
    (K : Finset (Finset ↥(active b)))
    (hd : F.val.deleted = deleted b ∪ liftEdge (active b) D)
    (hm : F.markers = K.image (liftEdge (active b))) (hq : F.val.relative = none) :
    F.cycleCount H = cycleOnCount r (univ \ D) K
      (fixedPortHost (inducedHost (active b) H) (fixedPorts b)) := by
  have hc := BootstrapBaseSourceDictionary.frame_core_count_base b F H
    (liftEdge (active b) D) hd hq
  simpa only [hm, restrictEdges_liftEdges, restrict_liftEdge,
    host_eq_fixedPortHost b H hH] using hc

theorem relative_count (b : Base M) (F : Frame r M) (H : SimpleHypergraph V)
    (hH : H ⊆ completeEdges V r) (D : Finset ↥(active b))
    (K : Finset (Finset ↥(active b))) (a z v t : ↥(active b))
    (hp : ({a,z} : Finset ↥(active b)) ∈ K)
    (hv : ({v,t} : Finset ↥(active b)) ∈ K)
    (hd : F.val.deleted = deleted b ∪ liftEdge (active b) D)
    (hm : F.markers = K.image (liftEdge (active b)))
    (hroot : F.val.root = (a.val,z.val)) (hq : F.val.relative = some (v.val,t.val)) :
    F.cycleCount H = directedCycleOnCount r (univ \ D) K
      (fixedPortHost (inducedHost (active b) H) (fixedPorts b))
      ⟨{a,z},hp⟩ ⟨{v,t},hv⟩ a v := by
  have ha : F.val.root.1 ∈ active b := by rw [hroot]; exact a.property
  have hc := BootstrapBaseSourceDictionary.frame_relative_count_base b F H
    (liftEdge (active b) D) (v.val,t.val) hd hq ha v.property
  simp only [restrict_liftEdge, host_eq_fixedPortHost b H hH] at hc
  have hm' : restrictEdges (active b) F.markers = K := by rw [hm, restrictEdges_liftEdges]
  subst K
  convert hc using 1 <;> simp [hroot, activeRestrictedMarker,
    restrictEdges_liftEdges, ← liftEdge_pair, restrict_liftEdge]

theorem completion_count_ambient (F : Frame r M) (H : SimpleHypergraph V)
    (c : Finset V × V × V) (hq : F.val.relative = none) :
    F.completionCount H c = directedCycleOnCount r (F.active \ c.1)
      (insert {c.2.1,c.2.2} F.markers) (H ∩ allowedEdges r (originalPorts M))
      ⟨{F.val.root.1,F.val.root.2},mem_insert_of_mem F.property.root_mem⟩
      ⟨{c.2.1,c.2.2},mem_insert_self _ _⟩ F.val.root.1 c.2.1 := by
  unfold Frame.completionCount directedCycleOnCount
  apply congrArg Finset.card
  ext E
  rw [F.mem_completionFamily, mem_directedCycleOnFamily, mem_cycleOnFamily]
  simp only [Frame.Directed, hq, Option.mem_def, reduceCtorEq, false_implies, forall_const,
    implies_true, and_true]
  constructor
  · rintro ⟨hE,C,hroot,hpair⟩
    exact ⟨⟨⟨C⟩,fun e he => (mem_filter.mp (hE he)).1⟩,C,
      (starts_iff_marker_start C F.val.root _).mp hroot,
      (starts_iff_marker_start C c.2 _).mp hpair⟩
  · rintro ⟨⟨_,hE⟩,C,hroot,hpair⟩
    refine ⟨?_,C,(starts_iff_marker_start C F.val.root _).mpr hroot,
      (starts_iff_marker_start C c.2 _).mpr hpair⟩
    intro e he
    exact mem_filter.mpr ⟨hE he,(C.edge_subset_active he).trans sdiff_subset⟩

theorem completion_count (b : Base M) (F : Frame r M) (H : SimpleHypergraph V)
    (hH : H ⊆ completeEdges V r) (D Q : Finset ↥(active b))
    (K : Finset (Finset ↥(active b))) (a z v t : ↥(active b))
    (hp : ({a,z} : Finset ↥(active b)) ∈ K)
    (hd : F.val.deleted = deleted b ∪ liftEdge (active b) D)
    (hm : F.markers = K.image (liftEdge (active b)))
    (hroot : F.val.root = (a.val,z.val)) (hq : F.val.relative = none)
    (hcand : F.LegalCandidate (liftEdge (active b) Q,v.val,t.val)) :
    F.completionCount H (liftEdge (active b) Q,v.val,t.val) =
      directedCycleOnCount r (univ \ (D ∪ Q)) (insert {v,t} K)
      (fixedPortHost (inducedHost (active b) H) (fixedPorts b))
      ⟨{a,z},mem_insert_of_mem hp⟩ ⟨{v,t},mem_insert_self _ _⟩ a v := by
  let c : Finset V × V × V := (liftEdge (active b) Q,v.val,t.val)
  have hbase : F.active ⊆ active b := by
    intro w hw
    change w ∈ univ \ deleted b
    change w ∈ univ \ F.val.deleted at hw
    rw [hd] at hw
    exact mem_sdiff.mpr ⟨mem_univ _, fun h => (mem_sdiff.mp hw).2 (mem_union_left _ h)⟩
  have hsurv : ∀ e ∈ insert {c.2.1,c.2.2} F.markers, e ⊆ F.active \ c.1 := by
    intro e he w hw
    have hn := (mem_sdiff.mp (hcand.1.augmented_subset_active e he hw)).2
    refine mem_sdiff.mpr ⟨?_,hn⟩
    rcases mem_insert.mp he with rfl | he
    · exact hcand.2.1 (mem_union_right _ hw)
    · exact F.property.retained e he hw
  have hdel : restrictEdge (active b) (F.active \ c.1) = univ \ (D ∪ Q) := by
    have he : F.active \ c.1 = univ \ (deleted b ∪ liftEdge (active b) (D ∪ Q)) := by
      change (univ \ F.val.deleted) \ liftEdge (active b) Q = _
      rw [hd, liftEdge_union]
      ext w
      simp only [mem_sdiff,mem_univ,mem_union,true_and]
      tauto
    rw [he,BootstrapBaseSourceDictionary.restrict_base_active,restrict_liftEdge]
  have hs := directedCycleOnCount_restrictWithin (r := r) (active b) (F.active \ c.1)
    (sdiff_subset.trans hbase) (insert {c.2.1,c.2.2} F.markers)
    (H ∩ allowedEdges r (originalPorts M)) hsurv
    ⟨{F.val.root.1,F.val.root.2},mem_insert_of_mem F.property.root_mem⟩
    ⟨{c.2.1,c.2.2},mem_insert_self _ _⟩
    ⟨F.val.root.1,by rw [hroot]; exact a.property⟩ v
  rw [completion_count_ambient F H _ hq]
  change _ = _ at hs
  simp only [hdel] at hs
  rw [hs]
  have hm' : restrictEdges (active b) F.markers = K := by rw [hm,restrictEdges_liftEdges]
  subst K
  simp only [activeRestrictedMarker,hroot,c,Prod.fst,Prod.snd,restrictEdges,image_insert]
  simp only [← liftEdge_pair,restrict_liftEdge]
  change directedCycleOnCount r _ _ (host r H b) _ _ _ _ = _
  rw [host_eq_fixedPortHost b H hH]
  congr 1
  · simp only [image_insert,← liftEdge_pair,restrict_liftEdge]
  · apply (Subtype.heq_iff_coe_eq (fun e => by
      simp only [image_insert,← liftEdge_pair,restrict_liftEdge])).mpr
    rfl
  · apply (Subtype.heq_iff_coe_eq (fun e => by
      simp only [image_insert,← liftEdge_pair,restrict_liftEdge])).mpr
    rfl

end LooseHamilton.BootstrapEndpointResidualCounts
