module

public import HittingTimeLooseHamilton.BootstrapCompletionMaximum
public import HittingTimeLooseHamilton.BootstrapFilteredBaseHost

public section

noncomputable section
namespace LooseHamilton.BootstrapOrdinaryLabelTransport
open Finset BootstrapBases
variable {V : Type} [Fintype V] [DecidableEq V] {M : Finset (Finset V)}

@[expose] def vertex (v : V) : ↥(active (none : Base M)) := ⟨v,by simp⟩
@[expose] def label (a : Finset V × V × V) :
    Finset ↥(active (none : Base M)) × ↥(active (none : Base M)) × ↥(active (none : Base M)) :=
  (restrictEdge (active (none : Base M)) a.1,vertex a.2.1,vertex a.2.2)

theorem label_injective : Function.Injective (label (M:=M)) := by
  intro a b he
  have hp := congrArg (fun l => liftEdge (active (none : Base M)) l.1) he
  have hy := congrArg (fun l => l.2.1.val) he
  have hz := congrArg (fun l => l.2.2.val) he
  change liftEdge _ (restrictEdge _ a.1) = liftEdge _ (restrictEdge _ b.1) at hp
  rw [lift_restrictEdge _ _ (by simp),lift_restrictEdge _ _ (by simp)] at hp
  exact Prod.ext hp (Prod.ext hy hz)

@[simp] theorem block_card (a : Finset V × V × V) : (label (M:=M) a).1.card = a.1.card := by
  rw [← liftEdge_card (active (none : Base M))]
  exact congrArg Finset.card (lift_restrictEdge _ _ (by simp))

@[simp] theorem pair_restrict (y z : V) :
    restrictEdge (active (none : Base M)) {y,z} = {vertex (M:=M) y,vertex z} := by
  ext v
  simp [mem_restrictEdge,vertex,Subtype.ext_iff]

theorem legal {r : ℕ} (hM : IsPairMatching M) (a : Finset V × V × V)
    (hs : LegalPrivateCompletion r M a.1 {a.2.1,a.2.2}) :
    LegalPrivateCompletion r (restrictEdges (active (none : Base M)) (markers hM none))
      (label a).1 {(label a).2.1,(label a).2.2} := by
  refine ⟨by simpa using hs.private_card,?_,?_,?_⟩
  · have he := congrArg Finset.card (pair_restrict (M:=M) a.2.1 a.2.2)
    rw [← liftEdge_card (active (none : Base M)),lift_restrictEdge _ _ (by simp)] at he
    simpa [label] using he.symm.trans hs.pair_card
  · apply disjoint_left.mpr
    intro v hv hp
    apply disjoint_left.mp hs.private_pair_disjoint ((mem_restrictEdge _ _ _).mp hv)
    rcases (by simpa only [mem_insert,mem_singleton] using hp : v = (label a).2.1 ∨ v = (label a).2.2) with h|h <;> simp_all [label,vertex]
  · apply disjoint_left.mpr
    intro v hv hp
    obtain ⟨e,he,hve⟩ := mem_biUnion.mp hp
    obtain ⟨f,hf,rfl⟩ := mem_image.mp he
    apply disjoint_left.mp hs.ports_disjoint _ (mem_biUnion.mpr ⟨f,hf,(mem_restrictEdge _ _ _).mp hve⟩)
    rcases mem_union.mp hv with hv|hv
    · exact mem_union_left _ ((mem_restrictEdge _ _ _).mp hv)
    · rcases (by simpa only [mem_insert,mem_singleton] using hv : v = (label a).2.1 ∨ v = (label a).2.2) with h|h <;> simp_all [label,vertex]

theorem weight_eq {r : ℕ} (hM : IsPairMatching M) (H : SimpleHypergraph V)
    (hH : H ⊆ completeEdges V r) (a : Finset V × V × V) :
    BootstrapCompletionMaximum.weight (r:=r) (M:=M) H a =
    completionCount r (restrictEdges (active (none : Base M)) (markers hM none))
      (fixedPortHost (inducedHost (active (none : Base M)) H) (fixedPorts none))
      (label a).1 {(label a).2.1,(label a).2.2} := by
  have he := BootstrapBaseSourceDictionary.completionCount_base (r:=r) hM none H a.1 {a.2.1,a.2.2}
    (by simp)
  rw [host_eq_fixedPortHost none H hH,pair_restrict] at he
  simpa [BootstrapCompletionMaximum.weight,label] using he

end LooseHamilton.BootstrapOrdinaryLabelTransport
