module

public import HittingTimeLooseHamilton.FrameEntropyBridgeRoleFacts
public import HittingTimeLooseHamilton.FrameEntropyInstance

public section

noncomputable section
namespace LooseHamilton
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A root-normalised presentation tests the actual intrinsic ordinary role. -/
theorem rootedOrdinaryRole_iff_in_witness {r : ℕ} (hr : 3 ≤ r)
    {M E : Finset (Finset V)} (C : MixedCycleWitness r M E)
    (root : ↥M) (a : ↥root.val) (hroot : C.markerStart root = a)
    (e : Finset V) (u v : V) :
    rootedOrdinaryRole r M E root a e u v ↔
      ∃ he : e ∈ E,
        C.junction (C.slot.symm (.inr ⟨_,he⟩)) = u ∧
        C.junction (finRotate C.length (C.slot.symm (.inr ⟨_,he⟩))) = v := by
  constructor
  · rintro ⟨D,hD,he,hu,hv⟩
    exact ⟨he,(C.slot_start_eq_of_root D hr root (hroot.trans hD.symm) _).trans hu,
      (C.slot_end_eq_of_root D hr root (hroot.trans hD.symm) _).trans hv⟩
  · rintro ⟨he,hu,hv⟩
    exact ⟨C,hroot,he,hu,hv⟩

namespace AuxiliaryFrame.Frame
variable {r : ℕ} {original : Finset (Finset V)}

lemma numberedEdge_inj (F : Frame r original) {e f : Finset V}
    (he : e ⊆ F.active) (hf : f ⊆ F.active)
    (h : F.numberedEdge e = F.numberedEdge f) : e=f := by
  have hh := (Finset.image_injective F.vertexNumbering.injective) h
  have := congrArg (liftEdge F.active) hh
  simpa only [lift_restrictEdge _ _ he,lift_restrictEdge _ _ hf] using this

lemma mem_numberedEdges_iff (F : Frame r original) {E : Finset (Finset V)}
    (hE : ∀ e ∈ E, e ⊆ F.active) {e : Finset V} (he : e ⊆ F.active) :
    F.numberedEdge e ∈ F.numberedEdges E ↔ e ∈ E := by
  constructor
  · intro h
    obtain ⟨a,ha,hh⟩ := mem_image.mp h
    obtain ⟨b,hb,rfl⟩ := mem_image.mp ha
    have hbe : b=e := F.numberedEdge_inj (hE b hb) he hh
    exact hbe ▸ hb
  · intro h
    exact mem_image_of_mem _ (mem_image_of_mem _ h)

end AuxiliaryFrame.Frame
end LooseHamilton
