module

public import HittingTimeLooseHamilton.BootstrapBaseSourceDictionary
public import HittingTimeLooseHamilton.PrivateFrameSourceScale

public section

/-! The induced allowed host is exactly the host used by the registered tests
on actual uniform extension states. The original port set remains fixed.
-/
noncomputable section
namespace LooseHamilton.BootstrapBases
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem host_eq_fixedPortHost {r : ℕ} {M : Finset (Finset V)}
    (b : Base M) (H : SimpleHypergraph V) (hH : H ⊆ completeEdges V r) :
    host r H b = fixedPortHost (inducedHost (active b) H) (fixedPorts b) := by
  rw [host_eq]
  exact inter_allowed_eq_fixedPortHost _ _ (inducedHost_uniform hH _)

theorem host_subset_outer (r : ℕ) {M : Finset (Finset V)}
    (b : Base M) (H : SimpleHypergraph V) : host r H b ⊆ inducedHost (active b) H := by
  rw [host_eq]
  exact inter_subset_left

/-- The frame dictionary literally uses the filtered inner host of the
registered private-source test, not a differently filtered auxiliary host. -/
theorem frame_source_count_filtered {r : ℕ} {M : Finset (Finset V)}
    (hM : IsPairMatching M) (b : Base M) (F : AuxiliaryFrame.Frame r M)
    (H : SimpleHypergraph V) (hH : H ⊆ completeEdges V r) (P q : Finset V)
    (hd : F.val.deleted = deleted b ∪ P)
    (hm : F.markers = insert q (markers hM b)) (hrel : F.val.relative = none)
    (hq : q ⊆ active b) :
    F.cycleCount H = completionCount r (restrictEdges (active b) (markers hM b))
      (fixedPortHost (inducedHost (active b) H) (fixedPorts b))
      (restrictEdge (active b) P) (restrictEdge (active b) q) := by
  rw [BootstrapBaseSourceDictionary.frame_source_count_base hM b F H P q hd hm hrel hq,
    host_eq_fixedPortHost b H hH]

end LooseHamilton.BootstrapBases
