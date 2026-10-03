module

public import HittingTimeLooseHamilton.EndpointCutClassification
public import HittingTimeLooseHamilton.EndpointCutModels
public import HittingTimeLooseHamilton.EndpointSourcePorts

public section

/-! The two local patterns produce exactly the independent legal cut labels. -/
noncomputable section
namespace LooseHamilton
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace MixedCycleOnWitness
variable {r : ℕ} {M F : Finset (Finset V)} {P : Finset V} {y z : V}

private theorem oldPorts_junctions
    (C : MixedCycleOnWitness r (univ \ P) (insert {y,z} M) F) :
    originalPorts M ⊆ univ.image C.junction := by
  intro v hv
  obtain ⟨m, hm, hv⟩ := mem_biUnion.mp hv
  let m' : ↥(insert {y,z} M) := ⟨m, mem_insert_of_mem hm⟩
  have hs := C.slot_edge (C.slot.symm (.inl m'))
  simp only [C.slot.apply_symm_apply] at hs
  change v ∈ m'.val at hv
  rw [hs] at hv
  rcases mem_insert.mp hv with h | h
  · exact h ▸ mem_image_of_mem C.junction (mem_univ _)
  · exact mem_singleton.mp h ▸ mem_image_of_mem C.junction (mem_univ _)

private theorem private_deleted_disjoint
    (C : MixedCycleOnWitness r (univ \ P) (insert {y,z} M) F) (e : ↥F) :
    Disjoint (C.privateBlock e) P := by
  apply disjoint_left.mpr
  intro v hv hp
  exact (mem_sdiff.mp (C.private_subset_active e hv)).2 hp

private theorem private_named_disjoint
    (C : MixedCycleOnWitness r (univ \ P) (insert {y,z} M) F) (e : ↥F)
    (a : V) (hz : z ∈ univ.image C.junction) (hy : y ∈ univ.image C.junction)
    (ha : a ∈ univ.image C.junction) :
    Disjoint (C.privateBlock e) (P ∪ originalPorts M ∪ {y,z,a}) := by
  rw [disjoint_union_right, disjoint_union_right]
  refine ⟨⟨C.private_deleted_disjoint e,
    (C.junction_private_disjoint e).symm.mono_right C.oldPorts_junctions⟩, ?_⟩
  apply (C.junction_private_disjoint e).symm.mono_right
  intro v hv
  simp only [mem_insert, mem_singleton] at hv
  rcases hv with rfl | rfl | rfl
  · exact hy
  · exact hz
  · exact ha

/-- Select the legal Type I or Type II label from the normalized source cycle. -/
theorem select_endpoint_cut
    (C : MixedCycleOnWitness r (univ \ P) (insert {y,z} M) F)
    (hlarge : 6 ≤ C.length) (U : Finset V) (G : Finset (Finset V))
    (hports : EndpointSourcePorts U M y z)
    (hG : G ⊆ allowedEdges r U) (hF : F ⊆ G)
    (hroot : C.slot ⟨0, by omega⟩ = .inl ⟨{y,z}, mem_insert_self _ _⟩)
    (hz : C.junction ⟨0, by omega⟩ = z)
    (hy : C.junction ⟨1, by omega⟩ = y) :
    ∃ e₁ : ↥F, C.slot ⟨1, by omega⟩ = .inr e₁ ∧
      (EndpointCutLegalI r M G P y z
        (C.junction ⟨2, by omega⟩, C.privateBlock e₁) ∨
       ∃ (m : ↥(insert {y,z} M)) (e₂ : ↥F),
        C.slot ⟨2, by omega⟩ = .inl m ∧ C.slot ⟨3, by omega⟩ = .inr e₂ ∧
        EndpointCutLegalII r M G P y z
          (C.junction ⟨2, by omega⟩, C.junction ⟨3, by omega⟩,
           C.junction ⟨4, by omega⟩, C.privateBlock e₁, C.privateBlock e₂)) := by
  have hold : ∀ m ∈ insert {y,z} M, m ≠ {y,z} → m ⊆ U := by
    intro m hm hne v hv
    apply hports.old_ports
    exact mem_biUnion.mpr ⟨m, (mem_insert.mp hm).resolve_left hne, hv⟩
  have hallowed : ∀ e ∈ F, (e ∩ U).card ≤ 1 := by
    intro e he
    exact (mem_allowedEdges r U e |>.mp (hG (hF he))).2
  obtain ⟨e₁,he₁,hcases⟩ := C.endpoint_cut_types hlarge
    ⟨{y,z}, mem_insert_self _ _⟩ U hroot hports.marked_in_source hold hallowed
  refine ⟨e₁,he₁,?_⟩
  have hzj : z ∈ univ.image C.junction  := mem_image.mpr ⟨⟨0, by omega⟩, mem_univ _, hz⟩
  have hyj : y ∈ univ.image C.junction  := mem_image.mpr ⟨⟨1, by omega⟩, mem_univ _, hy⟩
  have fresh (i : Fin C.length) (hi0 : i.val ≠ 0) (hi1 : i.val ≠ 1)
      (hU : C.junction i ∉ U) : C.junction i ∉ P ∪ originalPorts M ∪ {y,z} := by
    intro h
    rcases mem_union.mp h with h | h
    · rcases mem_union.mp h with h | h
      · exact (mem_sdiff.mp (C.junction_mem i)).2 h
      · exact hU (hports.old_ports h)
    · rcases mem_insert.mp h with h | h
      · have heq := C.junction_injective (h.trans hy.symm)
        exact hi1 (congrArg Fin.val heq)
      · have heq := C.junction_injective ((mem_singleton.mp h).trans hz.symm)
        exact hi0 (congrArg Fin.val heq)
  have edge₁ : e₁.val = {y, C.junction ⟨2, by omega⟩} ∪ C.privateBlock e₁ := by
    have hs := C.slot_edge ⟨1, by omega⟩
    rw [he₁] at hs
    simpa only [rotate_mk_succ (n := C.length) (k := 1) (by omega), hy] using hs
  rcases hcases with hI | ⟨m,e₂,hmr,hm,he₂,hII⟩
  · left
    refine ⟨fresh ⟨2, by omega⟩ (by simp) (by simp) hI,
      C.private_card e₁, C.private_named_disjoint e₁ _ hzj hyj
        (mem_image_of_mem _ (mem_univ _)), ?_⟩
    change {y, C.junction _} ∪ C.privateBlock e₁ ∈ G
    rw [← edge₁]
    exact hF e₁.property
  · right
    refine ⟨m,e₂,hm,he₂,?_⟩
    have hmM : m.val ∈ M := (mem_insert.mp m.property).resolve_left hmr
    have old : m.val = {C.junction ⟨2, by omega⟩, C.junction ⟨3, by omega⟩} := by
      have hs := C.slot_edge ⟨2, by omega⟩
      rw [hm] at hs
      simpa only [rotate_mk_succ (n := C.length) (k := 2) (by omega)] using hs
    have edge₂ : e₂.val = {C.junction ⟨3, by omega⟩, C.junction ⟨4, by omega⟩} ∪
        C.privateBlock e₂ := by
      have hs := C.slot_edge ⟨3, by omega⟩
      rw [he₂] at hs
      simpa only [rotate_mk_succ (n := C.length) (k := 3) (by omega)] using hs
    have he12 : e₁ ≠ e₂ := by
      intro h
      have hidx := C.slot.injective (he₁.trans (congrArg Sum.inr h) |>.trans he₂.symm)
      have hbad : (1 : ℕ) = 3 := congrArg Fin.val hidx
      omega
    refine ⟨?_, ?_, fresh ⟨4, by omega⟩ (by simp) (by simp) hII,
      C.private_card e₁, C.private_card e₂, C.private_disjoint he12,
      C.private_named_disjoint e₁ _ hzj hyj (mem_image_of_mem _ (mem_univ _)),
      C.private_named_disjoint e₂ _ hzj hyj (mem_image_of_mem _ (mem_univ _)), ?_, ?_⟩
    · change {C.junction _, C.junction _} ∈ M
      rw [← old]
      exact hmM
    · intro h
      have heq := C.junction_injective h
      have hbad : (2 : ℕ) = 3 := congrArg Fin.val heq
      omega
    · change {y,C.junction _} ∪ C.privateBlock e₁ ∈ G
      rw [← edge₁]
      exact hF e₁.property
    · change {C.junction _,C.junction _} ∪ C.privateBlock e₂ ∈ G
      rw [← edge₂]
      exact hF e₂.property

end MixedCycleOnWitness
end LooseHamilton
