module

public import HittingTimeLooseHamilton.FrameEntropyBiasedInstance
public import HittingTimeLooseHamilton.CompletionMatching

public section

noncomputable section
namespace LooseHamilton.AuxiliaryFrame.Frame
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {r : ℕ} {original : Finset (Finset V)}

@[expose] def completionActive (F : Frame r original) (c : Finset V × V × V) := F.active \ c.1
@[expose] def completionMarkers (F : Frame r original) (c : Finset V × V × V) := insert {c.2.1,c.2.2} F.markers
@[expose] def completionRawHost (F : Frame r original) (H : SimpleHypergraph V) (c : Finset V × V × V) :=
  (F.rawHost H).filter (fun e => e ⊆ F.completionActive c)
@[expose] def completionNumbering (F : Frame r original) (c : Finset V × V × V) :
    ↥(F.completionActive c) ≃ Fin (F.completionActive c).card :=
  (Fintype.equivFin _).trans (finCongr (by simp))
@[expose] def completionNumberedEdges (F : Frame r original) (c : Finset V × V × V)
    (E : SimpleHypergraph V) :=
  vertexEdges (F.completionNumbering c) (restrictEdges (F.completionActive c) E)

lemma completion_markers_supported (F : Frame r original) {c : Finset V × V × V}
    (hc : F.LegalCandidate c) :
    ∀ e ∈ F.completionMarkers c, e ⊆ F.completionActive c := by
  intro e he x hx
  rcases mem_insert.mp he with rfl | he
  · exact mem_sdiff.mpr ⟨hc.2.1 (mem_union_right _ hx), fun hp =>
      disjoint_left.mp hc.1.private_pair_disjoint hp hx⟩
  · exact mem_sdiff.mpr ⟨F.property.retained e he hx, fun hp =>
      disjoint_left.mp hc.1.ports_disjoint (mem_union_left _ hp) (mem_biUnion.mpr ⟨e,he,hx⟩)⟩

lemma completionNumberedEdges_card (F : Frame r original) (c : Finset V × V × V)
    (E : SimpleHypergraph V) (hE : ∀ e∈E, e⊆F.completionActive c) :
    (F.completionNumberedEdges c E).card=E.card := by
  rw [completionNumberedEdges,vertexEdges_card]
  have hh := Fintype.card_congr (restrictedEdgeEquiv (F.completionActive c) E hE)
  simpa using hh.symm

lemma completionNumberedEdges_inj (F : Frame r original) (c : Finset V × V × V)
    {E G : SimpleHypergraph V}
    (hE : ∀ e∈E, e⊆F.completionActive c) (hG : ∀ e∈G, e⊆F.completionActive c)
    (h : F.completionNumberedEdges c E=F.completionNumberedEdges c G) : E=G := by
  have hh := (Finset.image_injective (Finset.image_injective (F.completionNumbering c).injective)) h
  have hh' := congrArg (Finset.image (liftEdge (F.completionActive c))) hh
  rwa [liftEdges_restrictEdges _ _ hE,liftEdges_restrictEdges _ _ hG] at hh'

lemma completionNumberedEdges_uniform (F : Frame r original) (H : SimpleHypergraph V)
    (c : Finset V × V × V) :
    F.completionNumberedEdges c (F.completionRawHost H c) ⊆ completeEdges (Fin (F.completionActive c).card) r := by
  intro e he
  obtain ⟨a,ha,rfl⟩ := mem_image.mp he
  obtain ⟨b,hb,rfl⟩ := mem_image.mp ha
  apply (mem_completeEdges _ _).mpr
  rw [card_image_of_injective _ (F.completionNumbering c).injective]
  rw [← liftEdge_card (F.completionActive c),lift_restrictEdge _ _ (mem_filter.mp hb).2]
  exact ((mem_allowedEdges _ _ _).mp (F.rawHost_original_prohibition H (mem_filter.mp hb).1)).1

lemma completion_family_supported (F : Frame r original) (H : SimpleHypergraph V)
    (c : Finset V × V × V) {E : SimpleHypergraph V} (hE : E∈F.completionFamily H c) :
    ∀ e∈E, e⊆F.completionActive c := by
  obtain ⟨_,C,_⟩ := (F.mem_completionFamily H c E).mp hE
  intro e he
  exact C.edge_subset_active he

lemma completion_family_subset_raw (F : Frame r original) (H : SimpleHypergraph V)
    (c : Finset V × V × V) {E : SimpleHypergraph V} (hE : E∈F.completionFamily H c) :
    E ⊆ F.completionRawHost H c := by
  intro e he
  exact mem_filter.mpr ⟨((F.mem_completionFamily H c E).mp hE).1 he,F.completion_family_supported H c hE e he⟩

@[expose] def completionNumberedCycle (F : Frame r original) (H : SimpleHypergraph V)
    (c : Finset V × V × V) (E : ↥(F.completionFamily H c)) :
    BiasedCycleState r (F.completionNumberedEdges c (F.completionMarkers c))
      (F.completionNumberedEdges c (F.completionRawHost H c)) := by
  refine ⟨F.completionNumberedEdges c E.val,?_⟩
  obtain ⟨_,C,_⟩ := (F.mem_completionFamily H c E.val).mp E.property
  have hs : F.completionNumberedEdges c E.val ⊆ F.completionNumberedEdges c (F.completionRawHost H c) :=
    image_subset_image (image_subset_image (F.completion_family_subset_raw H c E.property))
  apply (LooseHamilton.mem_cycleFamily _ _ _ _ _).mpr
  refine ⟨⟨C.restrict.relabelVia (F.completionNumbering c)⟩,hs,?_⟩
  rw [allowedEdges_empty]
  exact hs.trans (F.completionNumberedEdges_uniform H c)

lemma completionNumberedCycle_injective (F : Frame r original) (H : SimpleHypergraph V)
    (c : Finset V × V × V) : Function.Injective (F.completionNumberedCycle H c) := by
  intro E G h
  apply Subtype.ext
  exact F.completionNumberedEdges_inj c (F.completion_family_supported H c E.property)
    (F.completion_family_supported H c G.property) (congrArg Subtype.val h)

@[expose] def completionCycleLaw (F : Frame r original) (H : SimpleHypergraph V)
    (c : Finset V × V × V) (h : (F.completionFamily H c).Nonempty) :=
  letI : Nonempty ↥(F.completionFamily H c) := h.to_subtype
  (FiniteEntropy.uniform (A:=↥(F.completionFamily H c))).map (F.completionNumberedCycle H c)

lemma completionCycleLaw_entropy (F : Frame r original) (H : SimpleHypergraph V)
    (c : Finset V × V × V) (h : (F.completionFamily H c).Nonempty) :
    FiniteEntropy.entropy (F.completionCycleLaw H c h).mass = Real.log (F.completionCount H c) := by
  letI : Nonempty ↥(F.completionFamily H c) := h.to_subtype
  rw [completionCycleLaw,FiniteEntropy.Law.entropy_map_of_injective _ _
    (F.completionNumberedCycle_injective H c),FiniteEntropy.entropy_uniform]
  simp [completionCount]
end LooseHamilton.AuxiliaryFrame.Frame
