module

public import HittingTimeLooseHamilton.FrameEntropyRelabel
public import HittingTimeLooseHamilton.AuxiliaryFrameEntropy
public import HittingTimeLooseHamilton.KahnConditioning

public section

noncomputable section
namespace LooseHamilton.AuxiliaryFrame.Frame
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {r : ℕ} {original : Finset (Finset V)}

@[expose] def vertexNumbering (F : Frame r original) : ↥F.active ≃ Fin F.n :=
  (Fintype.equivFin ↥F.active).trans (finCongr (by simp [n]))

@[expose] def numberedEdges (F : Frame r original) (E : Finset (Finset V)) :=
  vertexEdges F.vertexNumbering (restrictEdges F.active E)

@[expose] def numberedEdge (F : Frame r original) (e : Finset V) :=
  (restrictEdge F.active e).image F.vertexNumbering

lemma numberedEdges_mono (F : Frame r original) {E H : Finset (Finset V)}
    (h : E ⊆ H) : F.numberedEdges E ⊆ F.numberedEdges H :=
  image_subset_image (image_subset_image h)

lemma numberedEdges_inj (F : Frame r original) {E H : Finset (Finset V)}
    (hE : ∀e∈E, e⊆F.active) (hH : ∀e∈H, e⊆F.active)
    (h : F.numberedEdges E = F.numberedEdges H) : E=H := by
  have hh := (Finset.image_injective (Finset.image_injective F.vertexNumbering.injective)) h
  have := congrArg (Finset.image (liftEdge F.active)) hh
  rw [liftEdges_restrictEdges _ _ hE, liftEdges_restrictEdges _ _ hH] at this
  exact this

lemma numberedEdge_card (F : Frame r original) (e : Finset V) (he : e⊆F.active) :
    (F.numberedEdge e).card=e.card := by
  rw [numberedEdge, card_image_of_injective _ F.vertexNumbering.injective]
  rw [← liftEdge_card F.active, lift_restrictEdge _ _ he]

lemma numberedEdges_uniform (F : Frame r original) (H : Finset (Finset V)) :
    F.numberedEdges (F.rawHost H) ⊆ completeEdges (Fin F.n) r := by
  intro e he
  obtain ⟨a,ha,rfl⟩ := mem_image.mp he
  obtain ⟨b,hb,rfl⟩ := mem_image.mp ha
  apply (mem_completeEdges _ _).mpr
  change (F.numberedEdge b).card=r
  rw [F.numberedEdge_card b (mem_filter.mp hb).2]
  exact ((mem_allowedEdges _ _ _).mp (F.rawHost_original_prohibition H hb)).1

@[expose] def numberedCycle (F : Frame r original) (H : Finset (Finset V))
    (E : ↥(F.cycleFamily H)) :
    BiasedCycleState r (F.numberedEdges F.markers) (F.numberedEdges (F.rawHost H)) := by
  refine ⟨F.numberedEdges E.val, ?_⟩
  obtain ⟨hE,C,hC⟩ := (F.mem_cycleFamily H E.val).mp E.property
  apply (LooseHamilton.mem_cycleFamily _ _ _ _ _).mpr
  refine ⟨⟨C.restrict.relabelVia F.vertexNumbering⟩, F.numberedEdges_mono hE, ?_⟩
  rw [allowedEdges_empty]
  exact (F.numberedEdges_mono hE).trans (F.numberedEdges_uniform H)

lemma numberedCycle_injective (F : Frame r original) (H : Finset (Finset V)) :
    Function.Injective (F.numberedCycle H) := by
  intro E G h
  apply Subtype.ext
  apply F.numberedEdges_inj
  · intro e he
    exact (mem_filter.mp (((F.mem_cycleFamily H E.val).mp E.property).1 he)).2
  · intro e he
    exact (mem_filter.mp (((F.mem_cycleFamily H G.val).mp G.property).1 he)).2
  · exact congrArg Subtype.val h

@[expose] def numberedCycleLaw (F : Frame r original) (H : Finset (Finset V))
    (h : (F.cycleFamily H).Nonempty) :
    FiniteEntropy.Law (BiasedCycleState r (F.numberedEdges F.markers)
      (F.numberedEdges (F.rawHost H))) := by
  letI : Nonempty ↥(F.cycleFamily H) := h.to_subtype
  exact (FiniteEntropy.uniform (A:=↥(F.cycleFamily H))).map (F.numberedCycle H)

lemma numberedCycleLaw_entropy (F : Frame r original) (H : Finset (Finset V))
    (h : (F.cycleFamily H).Nonempty) :
    FiniteEntropy.entropy (F.numberedCycleLaw H h).mass = Real.log (F.cycleCount H) := by
  letI : Nonempty ↥(F.cycleFamily H) := h.to_subtype
  rw [numberedCycleLaw, FiniteEntropy.Law.entropy_map_of_injective _ _
    (F.numberedCycle_injective H), FiniteEntropy.entropy_uniform]
  simp [cycleCount]

lemma numberedCycleLaw_event (F : Frame r original) (H : Finset (Finset V))
    (h : (F.cycleFamily H).Nonempty)
    (P : BiasedCycleState r (F.numberedEdges F.markers)
      (F.numberedEdges (F.rawHost H)) → Prop) :
    (F.numberedCycleLaw H h).event P =
      letI : Nonempty ↥(F.cycleFamily H) := h.to_subtype
      (FiniteEntropy.uniform (A:=↥(F.cycleFamily H))).event
        (fun E => P (F.numberedCycle H E)) := by
  exact FiniteEntropy.Law.event_map _ _ _

lemma numberedEdges_card (F : Frame r original) (E : Finset (Finset V))
    (hE : ∀e∈E, e⊆F.active) : (F.numberedEdges E).card=E.card := by
  have h := Fintype.card_congr ((restrictedEdgeEquiv F.active E hE).trans
    (vertexEdgeEquiv F.vertexNumbering (restrictEdges F.active E)))
  simpa [numberedEdges] using h.symm

@[expose] def rootMarker (F : Frame r original) : ↥F.markers :=
  ⟨{F.val.root.1,F.val.root.2}, F.property.root_mem⟩

@[expose] def rootPoint (F : Frame r original) : ↥F.rootMarker.val :=
  ⟨F.val.root.1, by simp [rootMarker]⟩

@[expose] def numberedRoot (F : Frame r original) : ↥(F.numberedEdges F.markers) :=
  vertexEdgeEquiv F.vertexNumbering (restrictEdges F.active F.markers)
    (activeRestrictedMarker F.active F.rootMarker)

@[expose] def numberedInitial (F : Frame r original) : ↥F.numberedRoot.val :=
  ⟨F.vertexNumbering ⟨F.val.root.1,
      F.property.retained _ F.property.root_mem (by simp)⟩,
    mem_image_of_mem _ ((mem_restrictEdge _ _ _).mpr (by simp [rootMarker]))⟩

end LooseHamilton.AuxiliaryFrame.Frame
