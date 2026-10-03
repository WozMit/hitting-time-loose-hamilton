module

public import HittingTimeLooseHamilton.BootstrapPrivateLinkGeometry

public section

noncomputable section
namespace LooseHamilton.BootstrapPrivateLinkGeometry
open Finset BootstrapBases
variable {V : Type} [Fintype V] [DecidableEq V]
variable {r : ℕ} {M : Finset (Finset V)}

theorem surviving_split (hM : IsPairMatching M) (hr : 3 ≤ r) (b : Base M)
    (S q : Finset ↥(active b)) (x t : ↥(active b)) (hS : S.card = r-3)
    (hs : LegalPrivateCompletion r (restrictEdges (active b) (markers hM b)) (insert x S) q)
    (ht : t.val ∉ exclusions b S q x) (e : Finset V)
    (he : e ∈ rootEdgeUniverse r x.val)
    (hn : e ∉ deletedRootCollisions r x.val ((exclusions b S q t).erase x.val)) :
    e ⊆ active b ∧ ∃ R uv,
      PrivateRootSplitLegal r (restrictEdges (active b) (markers hM b))
        (allowedEdges r (fixedPorts b)) S q x t ((restrictEdge (active b) e).erase x) R uv := by
  have havoid : e ⊆ univ \ (exclusions b S q t).erase x.val := by
    by_contra h
    exact hn (mem_filter.mpr ⟨he,h⟩)
  have hd : Disjoint (e.erase x.val) (exclusions b S q t) := by
    apply disjoint_left.mpr
    intro v hv hz
    exact (mem_sdiff.mp (havoid (mem_erase.mp hv).2)).2
      (mem_erase.mpr ⟨(mem_erase.mp hv).1,hz⟩)
  have hes : e ⊆ active b := by
    intro v hv
    apply mem_sdiff.mpr
    refine ⟨mem_univ _,?_⟩
    intro hD
    by_cases hx : v = x.val
    · exact (mem_sdiff.mp x.property).2 (hx ▸ hD)
    · exact disjoint_left.mp hd (mem_erase.mpr ⟨hx,hv⟩)
        (by simp only [exclusions, mem_union, mem_singleton]; tauto)
  refine ⟨hes,?_⟩
  obtain ⟨hxt,htU,htarget⟩ := target_legal hM hr b S q x t hS hs ht
  let A := (restrictEdge (active b) e).erase x
  have hxc : x ∈ restrictEdge (active b) e :=
    (mem_restrictEdge _ _ _).mpr ((mem_rootEdgeUniverse _ _ _).mp he).2
  have hcard : A.card = r-1 := by
    have hh := congrArg Finset.card (lift_restrictEdge (active b) e hes)
    rw [liftEdge_card] at hh
    dsimp [A]
    rw [card_erase_of_mem hxc, hh, ((mem_rootEdgeUniverse _ _ _).mp he).1]
  apply private_split_of_disjoint hr _ (fixedPorts b) S q A x t hS hcard
    (notMem_erase _ _) hxt hs htarget
  apply disjoint_left.mpr
  intro v hv hz
  have hv' : v.val ∈ e.erase x.val := by
    apply mem_erase.mpr
    refine ⟨?_,(mem_restrictEdge _ _ _).mp (mem_erase.mp hv).2⟩
    intro h; exact (mem_erase.mp hv).1 (Subtype.ext h)
  apply disjoint_left.mp hd hv'
  rcases mem_union.mp hz with hz | hz
  · rcases mem_union.mp hz with hz | hz
    · rcases mem_insert.mp hz with h | h
      · subst v; simp [exclusions]
      · have hm := mem_image_of_mem (fun w : ↥(active b) => w.val) h
        simp only [exclusions, mem_union, mem_singleton]
        exact Or.inl (Or.inl (Or.inl (Or.inr hm)))
    · obtain ⟨f,hf,hvf⟩ := mem_biUnion.mp hz
      rcases mem_insert.mp hf with rfl | hf
      · exact mem_union_right _ (mem_image_of_mem _ hvf)
      · have hp := marker_ports_subset hM b (mem_biUnion.mpr ⟨f,hf,hvf⟩)
        exact mem_union_left _ (mem_union_right _ ((mem_fixedPorts b v).mp hp))
  · exact mem_union_left _ (mem_union_right _ ((mem_fixedPorts b v).mp hz))

end LooseHamilton.BootstrapPrivateLinkGeometry
