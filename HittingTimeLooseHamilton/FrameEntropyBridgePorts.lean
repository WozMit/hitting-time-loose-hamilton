module

public import HittingTimeLooseHamilton.FrameEntropyBridgeNumbering

public section

noncomputable section
namespace LooseHamilton.AuxiliaryFrame.Frame
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {r : ℕ} {original : Finset (Finset V)}

lemma numberedPorts_eq_image (F : Frame r original) :
    originalPorts (F.numberedEdges F.markers) =
      (originalPorts F.markers).image F.numberVertex := by
  rw [F.numberedEdges_eq_image]
  ext x
  simp only [originalPorts, mem_biUnion, mem_image]
  constructor
  · rintro ⟨e,⟨a,ha,rfl⟩,hx⟩
    rw [F.numberedEdge_eq_image a (F.property.retained a ha)] at hx
    obtain ⟨v,hv,rfl⟩ := mem_image.mp hx
    exact ⟨v,⟨a,ha,hv⟩,rfl⟩
  · rintro ⟨v,⟨a,ha,hv⟩,rfl⟩
    refine ⟨F.numberedEdge a,⟨a,ha,rfl⟩,?_⟩
    rw [F.numberedEdge_eq_image a (F.property.retained a ha)]
    exact mem_image_of_mem _ hv

lemma numberedEdge_disjoint_ports (F : Frame r original) (e : Finset V)
    (he : e ⊆ F.active) :
    Disjoint (F.numberedEdge e) (originalPorts (F.numberedEdges F.markers)) ↔
      Disjoint e (originalPorts F.markers) := by
  rw [F.numberedEdge_eq_image e he, F.numberedPorts_eq_image]
  constructor
  · intro hd
    apply disjoint_left.mpr
    intro x hx hp
    exact (disjoint_left.mp hd) (mem_image_of_mem _ hx) (mem_image_of_mem _ hp)
  · intro hd
    apply disjoint_left.mpr
    intro x hx hp
    obtain ⟨u,hu,rfl⟩ := mem_image.mp hx
    obtain ⟨v,hv,hh⟩ := mem_image.mp hp
    have hvA : v ∈ F.active := by
      obtain ⟨a,ha,hva⟩ := mem_biUnion.mp hv
      exact F.property.retained a ha hva
    have huv := F.numberVertex_inj hvA (he hu) hh
    exact (disjoint_left.mp hd) hu (huv ▸ hv)

lemma entropyInstance_eligibleEdges (F : Frame r original) (H : Finset (Finset V))
    (hX : (F.cycleFamily H).Nonempty) :
    (F.entropyInstance H hX).eligibleEdges = F.numberedEdges (F.existingCandidateEdges H) := by
  classical
  change (F.numberedEdges (F.rawHost H)).filter
    (fun e => Disjoint e (originalPorts (F.numberedEdges F.markers))) = _
  rw [F.numberedEdges_eq_image (F.rawHost H),
    F.numberedEdges_eq_image (F.existingCandidateEdges H), filter_image]
  apply congrArg (Finset.image F.numberedEdge)
  ext e
  simp only [mem_filter, existingCandidateEdges]
  constructor
  · rintro ⟨he,hd⟩
    exact ⟨he,(F.numberedEdge_disjoint_ports e (mem_filter.mp he).2).mp hd⟩
  · rintro ⟨he,hd⟩
    exact ⟨he,(F.numberedEdge_disjoint_ports e (mem_filter.mp he).2).mpr hd⟩
end LooseHamilton.AuxiliaryFrame.Frame
