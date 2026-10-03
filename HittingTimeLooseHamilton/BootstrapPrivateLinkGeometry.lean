module

public import HittingTimeLooseHamilton.PrivateStructuralLinks
public import HittingTimeLooseHamilton.BootstrapPrivateCandidateLifting
public import HittingTimeLooseHamilton.DeletedRootCollision

public section

noncomputable section
namespace LooseHamilton.BootstrapPrivateLinkGeometry
open Finset BootstrapBases
variable {V : Type} [Fintype V] [DecidableEq V]
variable {r : ℕ} {M : Finset (Finset V)}

@[expose] def exclusions (b : Base M) (S q : Finset ↥(active b)) (t : ↥(active b)) : Finset V :=
  deleted b ∪ liftEdge (active b) S ∪ {t.val} ∪ originalPorts M ∪ liftEdge (active b) q

theorem exclusions_card_le (hM : IsPairMatching M) (hr : 3 ≤ r) (b : Base M)
    (S q : Finset ↥(active b)) (t : ↥(active b))
    (hS : S.card = r-3) (hq : q.card = 2) :
    (exclusions b S q t).card ≤ 2*M.card+r+1 := by
  have h1 := card_union_le (deleted b) (liftEdge (active b) S)
  have h2 := card_union_le (deleted b ∪ liftEdge (active b) S) {t.val}
  have h3 := card_union_le (deleted b ∪ liftEdge (active b) S ∪ {t.val}) (originalPorts M)
  have h4 := card_union_le (deleted b ∪ liftEdge (active b) S ∪ {t.val} ∪ originalPorts M) (liftEdge (active b) q)
  have hd := deleted_card_le b
  simp only [liftEdge_card, card_singleton, hM.ports_card, hS, hq] at *
  unfold exclusions
  omega

theorem marker_ports_subset (hM : IsPairMatching M) (b : Base M) :
    originalPorts (restrictEdges (active b) (markers hM b)) ⊆ fixedPorts b := by
  intro v hv
  obtain ⟨e,he,hve⟩ := mem_biUnion.mp hv
  obtain ⟨f,hf,rfl⟩ := mem_image.mp he
  apply (mem_fixedPorts b v).mpr
  apply mem_biUnion.mpr
  refine ⟨f, ?_, (mem_restrictEdge _ _ _).mp hve⟩
  cases b with
  | none => exact hf
  | some a => exact (mem_erase.mp hf).2

theorem target_legal (hM : IsPairMatching M) (hr : 3 ≤ r) (b : Base M)
    (S q : Finset ↥(active b)) (x t : ↥(active b)) (hS : S.card = r-3)
    (hs : LegalPrivateCompletion r (restrictEdges (active b) (markers hM b)) (insert x S) q)
    (ht : t.val ∉ exclusions b S q x) :
    x ≠ t ∧ t.val ∉ originalPorts M ∧
    LegalPrivateCompletion r (restrictEdges (active b) (markers hM b)) (insert t S) q := by
  have htS : t ∉ S := by
    intro h; apply ht; simp only [exclusions, mem_union, mem_singleton];
    exact Or.inl (Or.inl (Or.inl (Or.inr (mem_image_of_mem _ h))))
  have htq : t ∉ q := by
    intro h; exact ht (mem_union_right _ (mem_image_of_mem _ h))
  have htU : t.val ∉ originalPorts M := by
    intro h; exact ht (mem_union_left _ (mem_union_right _ h))
  have hxt : x ≠ t := by
    intro h; apply ht; subst t
    simp [exclusions]
  refine ⟨hxt,htU,?_,hs.pair_card,?_,?_⟩
  · rw [card_insert_of_notMem htS,hS]; omega
  · exact disjoint_insert_left.mpr ⟨htq, hs.private_pair_disjoint.mono_left (subset_insert _ _)⟩
  · apply disjoint_left.mpr
    intro v hv hp
    rcases mem_union.mp hv with hv | hv
    · rcases mem_insert.mp hv with rfl | hv
      · exact htU ((mem_fixedPorts b _).mp (marker_ports_subset hM b hp))
      · exact disjoint_left.mp hs.ports_disjoint (mem_union_left _ (mem_insert_of_mem hv)) hp
    · exact disjoint_left.mp hs.ports_disjoint (mem_union_right _ hv) hp

end LooseHamilton.BootstrapPrivateLinkGeometry
