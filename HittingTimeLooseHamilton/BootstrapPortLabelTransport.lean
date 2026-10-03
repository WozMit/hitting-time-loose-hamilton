module

public import HittingTimeLooseHamilton.BootstrapFilteredBaseHost
public import HittingTimeLooseHamilton.RootFreePortTests

public section

noncomputable section
namespace LooseHamilton.BootstrapPortLabelTransport
open Finset BootstrapBases
variable {V : Type} [Fintype V] [DecidableEq V] {M : Finset (Finset V)}

theorem weight_eq {r : ℕ} (hM : IsPairMatching M) (a : ↥(originalPorts M))
    (H : SimpleHypergraph V) (hH : H ⊆ completeEdges V r) (P q : Finset V)
    (hq : q ⊆ active (some a)) :
    rootFreePortCompletion r M (fixedPortHost H (originalPorts M)) a.val
      (OriginalPortPartner.partner hM a) P q =
    completionCount r (restrictEdges (active (some a)) (markers hM (some a)))
      (fixedPortHost (inducedHost (active (some a)) H) (fixedPorts (some a)))
      (restrictEdge (active (some a)) P) (restrictEdge (active (some a)) q) := by
  rw [rootFreePortCompletion_eq]
  have hs : (univ.erase a.val) \ P = univ \ (deleted (some a) ∪ P) := by
    ext v
    simp [deleted, and_assoc]
  rw [hs, ← inter_allowed_eq_fixedPortHost H (originalPorts M) hH]
  exact (BootstrapBaseSourceDictionary.completionCount_base hM (some a) H P q hq).trans
    (by rw [host_eq_fixedPortHost (some a) H hH])

@[expose] def partner (hM : IsPairMatching M) (a : ↥(originalPorts M)) : ↥(active (some a)) :=
  ⟨OriginalPortPartner.partner hM a, partner_survives hM a⟩

theorem pair_restrict (a : ↥(originalPorts M)) (y z : ↥(active (some a))) :
    restrictEdge (active (some a)) {y.val,z.val} = {y,z} := by
  ext v
  simp only [mem_restrictEdge, mem_insert, mem_singleton, Subtype.val_inj]

theorem legal {r : ℕ} (hM : IsPairMatching M) (a : ↥(originalPorts M))
    (P : Finset V) (y z : ↥(active (some a))) (hP : P ⊆ active (some a))
    (hs : LegalPrivateCompletion r (markers hM (some a)) P {y.val,z.val}) :
    LegalPrivateCompletion r (restrictEdges (active (some a)) (markers hM (some a)))
      (restrictEdge (active (some a)) P) {y,z} := by
  refine ⟨?_,?_,?_,?_⟩
  · rw [← liftEdge_card (active (some a)),lift_restrictEdge _ _ hP]
    exact hs.private_card
  · rw [← liftEdge_card (active (some a)),liftEdge_pair]
    exact hs.pair_card
  · apply disjoint_left.mpr
    intro v hv hp
    apply disjoint_left.mp hs.private_pair_disjoint ((mem_restrictEdge _ _ _).mp hv)
    simpa only [← pair_restrict a y z,mem_restrictEdge] using hp
  · apply disjoint_left.mpr
    intro v hv hp
    obtain ⟨e,he,hve⟩ := mem_biUnion.mp hp
    obtain ⟨f,hf,rfl⟩ := mem_image.mp he
    apply disjoint_left.mp hs.ports_disjoint _ (mem_biUnion.mpr ⟨f,hf,(mem_restrictEdge _ _ _).mp hve⟩)
    rcases mem_union.mp hv with hv|hv
    · exact mem_union_left _ ((mem_restrictEdge _ _ _).mp hv)
    · exact mem_union_right _ (by simpa only [← pair_restrict a y z,mem_restrictEdge] using hv)

@[expose] def vertex (hM : IsPairMatching M) (a : ↥(originalPorts M)) (u : V) : ↥(active (some a)) :=
  if h : u ≠ a.val then ⟨u,by simpa [active] using h⟩ else partner hM a

@[simp] theorem vertex_val (hM : IsPairMatching M) (a : ↥(originalPorts M))
    (u : V) (hu : u ≠ a.val) : (vertex hM a u).val = u := by
  simp [vertex,hu]

@[expose] def label (hM : IsPairMatching M) (a : ↥(originalPorts M)) (l : Finset V × V × V) :
    Finset ↥(active (some a)) × ↥(active (some a)) × ↥(active (some a)) :=
  (restrictEdge (active (some a)) l.1,vertex hM a l.2.1,partner hM a)

theorem block_card (hM : IsPairMatching M) (a : ↥(originalPorts M))
    (l : Finset V × V × V) (hP : a.val ∉ l.1) : (label hM a l).1.card = l.1.card := by
  change (restrictEdge (active (some a)) l.1).card = _
  rw [←liftEdge_card (active (some a)),lift_restrictEdge]
  intro v hv
  simp only [active,deleted,mem_sdiff,mem_univ,mem_singleton,true_and]
  exact fun he => hP (he ▸ hv)

end LooseHamilton.BootstrapPortLabelTransport
