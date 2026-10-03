module

public import HittingTimeLooseHamilton.BootstrapFrameMeanNormalization
public import HittingTimeLooseHamilton.BootstrapFilteredBaseHost

public section

/-! The actual ambient source frame has exactly the source count and filtered
mean on the fixed base used by the registered private test. -/
noncomputable section
namespace LooseHamilton.BootstrapPrivateSourceNormalization
open Finset BootstrapBases BootstrapMeans
variable {V : Type} [Fintype V] [DecidableEq V]
variable {r : ℕ} {M : Finset (Finset V)}

theorem base_source_active (b : Base M) (P : Finset ↥(active b)) :
    ambientEdge (active b) (univ \ P) =
      univ \ (deleted b ∪ liftEdge (active b) P) := by
  have hs : univ \ (deleted b ∪ liftEdge (active b) P) ⊆ active b := by
    intro v hv
    exact mem_sdiff.mpr ⟨mem_univ _,fun hd =>
      (mem_sdiff.mp hv).2 (mem_union_left _ hd)⟩
  have he := BootstrapBaseSourceDictionary.restrict_base_active b (liftEdge (active b) P)
  rw [restrict_liftEdge] at he
  rw [← he]
  exact ambientEdge_restrict _ _ hs

theorem frame_active_eq (b : Base M) (F : AuxiliaryFrame.Frame r M)
    (S : Finset ↥(active b)) (x : ↥(active b))
    (hd : F.val.deleted = deleted b ∪ liftEdge (active b) (insert x S)) :
    F.active = ambientEdge (active b) (univ \ insert x S) := by
  rw [base_source_active]
  exact congrArg (fun D => univ \ D) hd

theorem frame_source_count (hM : IsPairMatching M) (b : Base M)
    (F : AuxiliaryFrame.Frame r M) (H : SimpleHypergraph V)
    (hH : H ⊆ completeEdges V r) (S q : Finset ↥(active b)) (x : ↥(active b))
    (hd : F.val.deleted = deleted b ∪ liftEdge (active b) (insert x S))
    (hm : F.markers = insert (liftEdge (active b) q) (markers hM b))
    (hrel : F.val.relative = none) :
    F.cycleCount H = completionCount r (restrictEdges (active b) (markers hM b))
      (fixedPortHost (inducedHost (active b) H) (fixedPorts b)) (insert x S) q := by
  simpa only [restrict_liftEdge] using
    frame_source_count_filtered hM b F H hH (liftEdge (active b) (insert x S))
      (liftEdge (active b) q) hd hm hrel (liftEdge_subset _ _)

theorem frame_mu_eq_filtered_source (b : Base M) (F : AuxiliaryFrame.Frame r M)
    (H : SimpleHypergraph V) (hH : H ⊆ completeEdges V r)
    (S : Finset ↥(active b)) (x : ↥(active b))
    (hd : F.val.deleted = deleted b ∪ liftEdge (active b) (insert x S)) :
    F.mu H = privateRootSourceMean r
      (fixedPortHost (inducedHost (active b) H) (fixedPorts b)) S x := by
  rw [← host_eq_fixedPortHost b H hH]
  change F.mu H = privateRootSourceMean r
    (inducedHost (active b) (H ∩ allowedEdges r (originalPorts M))) S x
  rw [privateRootSourceMean_ambient, ← frame_active_eq b F S x hd]
  exact F.mu_eq_filtered_inducedMean H

theorem frame_mu_le_outer_source (b : Base M) (F : AuxiliaryFrame.Frame r M)
    (H : SimpleHypergraph V) (S : Finset ↥(active b)) (x : ↥(active b))
    (hd : F.val.deleted = deleted b ∪ liftEdge (active b) (insert x S)) :
    F.mu H ≤ privateRootSourceMean r (inducedHost (active b) H) S x := by
  rw [privateRootSourceMean_ambient, ← frame_active_eq b F S x hd]
  exact F.mu_le_outer_inducedMean H

/-- The source mean is positive and the frame mean is favorable. Positivity is
obtained from the actual registered completion count, without an entropy budget. -/
theorem positive_source_normalization (hM : IsPairMatching M) (b : Base M)
    (F : AuxiliaryFrame.Frame r M) (hr : 3 ≤ r) (H : SimpleHypergraph V)
    (hH : H ⊆ completeEdges V r) (S q : Finset ↥(active b)) (x : ↥(active b))
    (hd : F.val.deleted = deleted b ∪ liftEdge (active b) (insert x S))
    (hm : F.markers = insert (liftEdge (active b) q) (markers hM b))
    (hrel : F.val.relative = none)
    (hW : 0 < completionCount r (restrictEdges (active b) (markers hM b))
      (fixedPortHost (inducedHost (active b) H) (fixedPorts b)) (insert x S) q) :
    0 < F.mu H ∧ F.mu H ≤ privateRootSourceMean r (inducedHost (active b) H) S x ∧
      0 < privateRootSourceMean r (inducedHost (active b) H) S x := by
  have hw : 0 < F.cycleCount H := by
    rw [frame_source_count hM b F H hH S q x hd hm hrel]
    exact hW
  have hp := F.mu_pos_of_cycleCount_pos hr H hw
  have hl := frame_mu_le_outer_source b F H S x hd
  exact ⟨hp,hl,hp.trans_le hl⟩

end LooseHamilton.BootstrapPrivateSourceNormalization
