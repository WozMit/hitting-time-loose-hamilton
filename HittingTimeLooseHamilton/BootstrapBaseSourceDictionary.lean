module

public import HittingTimeLooseHamilton.BootstrapNestedRestriction
public import HittingTimeLooseHamilton.BootstrapActualSourceFrames

public section

/-! Exact transport of actual completion sources into their fixed base subtype. -/
noncomputable section
namespace LooseHamilton.BootstrapBaseSourceDictionary
open Finset BootstrapBases
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {r : ℕ} {M : Finset (Finset V)}

/-- Restricting the surviving active set performs only the additional private deletion. -/
theorem restrict_base_active (b : Base M) (P : Finset V) :
    restrictEdge (active b) (univ \ (deleted b ∪ P)) =
      univ \ restrictEdge (active b) P := by
  ext v
  have hv := (mem_sdiff.mp v.property).2
  simp only [mem_restrictEdge,mem_sdiff,mem_univ,mem_union,true_and]
  exact ⟨fun h hp => h (Or.inr hp),fun h hp => hp.elim hv h⟩

/-- Literal ambient completion counts equal those on the ordinary/original-port
base, with the original forbidden-port filter unchanged. -/
theorem completionCount_base (hM : IsPairMatching M) (b : Base M)
    (H : SimpleHypergraph V) (P q : Finset V) (hq : q ⊆ active b) :
    completionCount r (markers hM b) (H ∩ allowedEdges r (originalPorts M))
      (deleted b ∪ P) q =
    completionCount r (restrictEdges (active b) (markers hM b)) (host r H b)
      (restrictEdge (active b) P) (restrictEdge (active b) q) := by
  unfold completionCount
  have hSA : univ \ (deleted b ∪ P) ⊆ active b := by
    intro v hv
    exact mem_sdiff.mpr ⟨mem_univ _,fun h =>
      (mem_sdiff.mp hv).2 (mem_union_left _ h)⟩
  have hm : ∀ e ∈ insert q (markers hM b), e ⊆ active b := by
    intro e he
    rcases mem_insert.mp he with rfl | he
    · exact hq
    · exact markers_retained hM b he
  rw [cycleOnCount_restrictWithin r _ (active b) hSA _ _ hm,
    restrict_base_active]
  simp only [restrictEdges,image_insert,host]

/-- Subtype private blocks and pairs lift back to exactly the same ambient source. -/
theorem completionCount_lifted_base (hM : IsPairMatching M) (b : Base M)
    (H : SimpleHypergraph V) (P q : Finset ↥(active b)) :
    completionCount r (markers hM b) (H ∩ allowedEdges r (originalPorts M))
      (deleted b ∪ liftEdge (active b) P) (liftEdge (active b) q) =
    completionCount r (restrictEdges (active b) (markers hM b)) (host r H b) P q := by
  simpa only [restrict_liftEdge] using
    completionCount_base hM b H (liftEdge (active b) P) (liftEdge (active b) q)
      (liftEdge_subset _ _)

/-- A realized source frame is exactly the completion source used by the
base-indexed registry, not just an analogous ambient expression. -/
theorem frame_source_count_base (hM : IsPairMatching M) (b : Base M)
    (F : AuxiliaryFrame.Frame r M) (H : SimpleHypergraph V) (P q : Finset V)
    (hd : F.val.deleted = deleted b ∪ P)
    (hm : F.markers = insert q (markers hM b)) (hrel : F.val.relative = none)
    (hq : q ⊆ active b) :
    F.cycleCount H = completionCount r (restrictEdges (active b) (markers hM b))
      (host r H b) (restrictEdge (active b) P) (restrictEdge (active b) q) := by
  rw [F.cycleCount_private_source hrel H (markers hM b) _ _ hd hm]
  exact completionCount_base hM b H P q hq

end LooseHamilton.BootstrapBaseSourceDictionary
