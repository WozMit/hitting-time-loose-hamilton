module

public import HittingTimeLooseHamilton.FrameEntropyBiasedInstance
public import HittingTimeLooseHamilton.IndexedSurvivalOverlapLaw
public import HittingTimeLooseHamilton.CoarseOverlapMain

public section

noncomputable section
namespace FiniteEntropy.Law
open Finset

lemma independentOverlap_map {A B V : Type*} [Fintype A] [Fintype B]
    [Fintype V] [DecidableEq V] (p : Law A) (f : A → B) (S : B → Finset V) :
    (p.map f).independentOverlap S = p.independentOverlap (fun a => S (f a)) := by
  classical
  rw [independentOverlap_eq_sum_sq,independentOverlap_eq_sum_sq]
  simp only [event_map]

end FiniteEntropy.Law
namespace LooseHamilton.AuxiliaryFrame.Frame
open Finset FiniteEntropy
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {r : ℕ} {original : Finset (Finset V)}

lemma numberedEdges_inter (F : Frame r original) (E G : Finset (Finset V))
    (hE : ∀e∈E, e⊆F.active) (hG : ∀e∈G, e⊆F.active) :
    F.numberedEdges E ∩ F.numberedEdges G = F.numberedEdges (E∩G) := by
  classical
  apply Finset.Subset.antisymm
  · intro e he
    obtain ⟨a,ha,hae⟩ := mem_image.mp (mem_inter.mp he).1
    obtain ⟨b,hb,hbe⟩ := mem_image.mp (mem_inter.mp he).2
    obtain ⟨c,hc,rfl⟩ := mem_image.mp ha
    obtain ⟨d,hd,rfl⟩ := mem_image.mp hb
    have hab : restrictEdge F.active c = restrictEdge F.active d :=
      Finset.image_injective F.vertexNumbering.injective (hae.trans hbe.symm)
    have hcd : c=d := by
      have hh := congrArg (liftEdge F.active) hab
      simpa only [lift_restrictEdge _ _ (hE c hc),lift_restrictEdge _ _ (hG d hd)] using hh
    exact mem_image.mpr ⟨restrictEdge F.active c,
      mem_image.mpr ⟨c,mem_inter.mpr ⟨hc,hcd ▸ hd⟩,rfl⟩,hae⟩
  · exact subset_inter (F.numberedEdges_mono inter_subset_left)
      (F.numberedEdges_mono inter_subset_right)

/-- Relabelling the active vertices preserves the actual family overlap,
including the diagonal and all prescribed direction restrictions. -/
theorem uniformOverlap_eq_entropyInstance (F : Frame r original)
    (H : SimpleHypergraph V) (hF : (F.cycleFamily H).Nonempty) :
    IndexedSurvival.uniformOverlap (F.cycleFamily H) id =
      (F.entropyInstance H hF).ordinaryOverlap := by
  classical
  letI : Nonempty ↥(F.cycleFamily H) := hF.to_subtype
  rw [IndexedSurvival.uniformOverlap_eq_independent _ _ hF]
  change _ = (uniform.map (F.numberedCycle H)).independentOverlap Subtype.val
  rw [Law.independentOverlap_map]
  unfold Law.independentOverlap
  apply sum_congr rfl
  intro E _
  apply sum_congr rfl
  intro G _
  have hE : ∀e∈E.val,e⊆F.active := fun e he =>
    (mem_filter.mp (((F.mem_cycleFamily H E.val).mp E.property).1 he)).2
  have hG : ∀e∈G.val,e⊆F.active := fun e he =>
    (mem_filter.mp (((F.mem_cycleFamily H G.val).mp G.property).1 he)).2
  change _ = _ * _ * ((F.numberedEdges E.val ∩ F.numberedEdges G.val).card:ℝ)
  rw [F.numberedEdges_inter _ _ hE hG,
    F.numberedEdges_card _ (fun e he => hE e (mem_inter.mp he).1)]
  rfl
end LooseHamilton.AuxiliaryFrame.Frame
