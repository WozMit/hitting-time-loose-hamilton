module

public import HittingTimeLooseHamilton.FrameCompletionInstanceBiased
public import HittingTimeLooseHamilton.FrameCoarseMainTransport

public section

noncomputable section
namespace LooseHamilton.AuxiliaryFrame.Frame
open Finset FiniteEntropy
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {r : ℕ} {original : Finset (Finset V)}

lemma completionNumberedEdges_inter (F : Frame r original) (c : Finset V × V × V) (E G : Finset (Finset V))
    (hE : ∀e∈E, e⊆(F.completionActive c)) (hG : ∀e∈G, e⊆(F.completionActive c)) :
    F.completionNumberedEdges c E ∩ F.completionNumberedEdges c G = F.completionNumberedEdges c (E∩G) := by
  classical
  apply Finset.Subset.antisymm
  · intro e he
    obtain ⟨a,ha,hae⟩ := mem_image.mp (mem_inter.mp he).1
    obtain ⟨b,hb,hbe⟩ := mem_image.mp (mem_inter.mp he).2
    obtain ⟨x,hc,rfl⟩ := mem_image.mp ha
    obtain ⟨d,hd,rfl⟩ := mem_image.mp hb
    have hab : restrictEdge (F.completionActive c) x = restrictEdge (F.completionActive c) d :=
      Finset.image_injective (F.completionNumbering c).injective (hae.trans hbe.symm)
    have hcd : x=d := by
      have hh := congrArg (liftEdge (F.completionActive c)) hab
      simpa only [lift_restrictEdge _ _ (hE x hc),lift_restrictEdge _ _ (hG d hd)] using hh
    exact mem_image.mpr ⟨restrictEdge (F.completionActive c) x,
      mem_image.mpr ⟨x,mem_inter.mpr ⟨hc,hcd ▸ hd⟩,rfl⟩,hae⟩
  · exact subset_inter (image_subset_image (image_subset_image inter_subset_left))
      (image_subset_image (image_subset_image inter_subset_right))


/-- Exact preservation of the actual prescribed-direction completion overlap. -/
theorem uniformOverlap_eq_completionEntropyInstance (F : Frame r original)
    (H : SimpleHypergraph V) (c : Finset V × V × V) (hc : F.LegalCandidate c)
    (hY : (F.completionFamily H c).Nonempty) :
    IndexedSurvival.uniformOverlap (F.completionFamily H c) id =
      (F.completionEntropyInstance H c hc hY).ordinaryOverlap := by
  classical
  letI : Nonempty ↥(F.completionFamily H c) := hY.to_subtype
  rw [IndexedSurvival.uniformOverlap_eq_independent _ _ hY]
  change _ = (uniform.map (F.completionNumberedCycle H c)).independentOverlap Subtype.val
  rw [Law.independentOverlap_map]
  unfold Law.independentOverlap
  apply sum_congr rfl
  intro E _
  apply sum_congr rfl
  intro G _
  have hE := F.completion_family_supported H c E.property
  have hG := F.completion_family_supported H c G.property
  change _ = _ * _ * ((F.completionNumberedEdges c E.val ∩ F.completionNumberedEdges c G.val).card:ℝ)
  rw [F.completionNumberedEdges_inter c _ _ hE hG,
    F.completionNumberedEdges_card c _ (fun e he => hE e (mem_inter.mp he).1)]
  rfl
end LooseHamilton.AuxiliaryFrame.Frame
