module

public import HittingTimeLooseHamilton.BiasedRoleHostBias
public import HittingTimeLooseHamilton.BiasedCloneHostEligible
public import HittingTimeLooseHamilton.BiasedCloneHostProperties

public section

/-! Eligible directed-role coordinates embed injectively into actual clone edges. -/
noncomputable section
open Finset FiniteEntropy
open scoped BigOperators
namespace LooseHamilton
variable {V : Type*} [Fintype V] [DecidableEq V]

abbrev EligibleRoleCoordinate (markers G : SimpleHypergraph V) :=
  (e : ↥(eligibleRoleEdges markers G)) × ↥e.val.offDiag

@[expose] def roleCloneEdge {markers G : SimpleHypergraph V}
    (i : EligibleRoleCoordinate markers G) : Finset (V × Fin 3) :=
  directedCloneEdge i.1.val i.2.val.1 i.2.val.2

lemma roleCloneEdge_project {markers G : SimpleHypergraph V}
    (i : EligibleRoleCoordinate markers G) : (roleCloneEdge i).image Prod.fst = i.1.val :=
  directedCloneEdge_project _ (mem_offDiag.mp i.2.property).1 (mem_offDiag.mp i.2.property).2.1

lemma roleCloneEdge_injective {markers G : SimpleHypergraph V} :
    Function.Injective (roleCloneEdge : EligibleRoleCoordinate markers G → _) := by
  intro i j h
  have hp := congrArg (fun B : Finset (V × Fin 3) => B.image Prod.fst) h
  rw [roleCloneEdge_project, roleCloneEdge_project] at hp
  obtain ⟨⟨E,hE⟩,⟨uv,huv⟩⟩ := i
  obtain ⟨⟨F,hF⟩,⟨st,hst⟩⟩ := j
  dsimp only at hp
  subst F
  have hp' : uv = st := directedCloneEdge_injective E h
  subst st
  rfl

lemma roleCloneEdge_mem_host_iff {markers G : SimpleHypergraph V}
    (U : Finset (V × Fin 3)) (i : EligibleRoleCoordinate markers G) :
    roleCloneEdge i ∈ cloneHost G U ↔ roleCloneEdge i ⊆ U := by
  constructor
  · exact fun h => (mem_filter.mp h).2
  · intro h
    apply mem_filter.mpr
    refine ⟨mem_biUnion.mpr ⟨i.1.val, (mem_filter.mp i.1.property).1, ?_⟩, h⟩
    apply mem_image.mpr
    refine ⟨i.2.val, mem_filter.mpr ⟨?_, (mem_offDiag.mp i.2.property).2.2⟩, rfl⟩
    exact mem_product.mpr ⟨(mem_offDiag.mp i.2.property).1, (mem_offDiag.mp i.2.property).2.1⟩

lemma roleCloneEdge_subset_iff {r : ℕ} {markers G : SimpleHypergraph V}
    (root : ↥markers) (a : ↥root.val) (C : ConnectedCloneCycle r markers)
    (i : EligibleRoleCoordinate markers G) :
    roleCloneEdge i ⊆ (C.directedWitness root a).cloneVertices ↔
      ∀ w ∈ i.1.val, w ∈ (ConnectedCloneCycle.role root a C).1 ↔
        w=i.2.val.1 ∨ w=i.2.val.2 := by
  have hu := (mem_offDiag.mp i.2.property).1
  have hv := (mem_offDiag.mp i.2.property).2.1
  have hp := (mem_filter.mp i.1.property).2
  rw [roleCloneEdge,
    (C.directedWitness root a).eligible_directedCloneEdge_subset_iff _ hu hv hp]
  change i.1.val ∩ _ = _ ↔ ∀ w ∈ i.1.val, w ∈ _ \ originalPorts markers ↔ _
  constructor
  · intro h w hw
    have he := congrArg (fun s : Finset V => w∈s) h
    have hn : w∉originalPorts markers := disjoint_left.mp hp hw
    simpa only [mem_inter, hw, true_and, mem_insert, mem_singleton,
      mem_sdiff, hn, not_false_eq_true, and_true] using iff_of_eq he
  · intro h
    ext w
    by_cases hw : w∈i.1.val
    · have hn : w∉originalPorts markers := disjoint_left.mp hp hw
      have hh := h w hw
      simpa only [mem_inter, hw, true_and, mem_insert, mem_singleton,
        mem_sdiff, hn, not_false_eq_true, and_true] using hh
    · have hwu : w≠i.2.val.1 := fun he => hw (he ▸ hu)
      have hwv : w≠i.2.val.2 := fun he => hw (he ▸ hv)
      simp [hw, hwu, hwv]

lemma roleCloneEdge_sum_le {markers G : SimpleHypergraph V}
    (U : Finset (V × Fin 3)) (g : Finset (V × Fin 3) → ℝ)
    (hg : ∀ B ∈ cloneHost G U, 0 ≤ g B) :
    (∑ i : EligibleRoleCoordinate markers G,
      if roleCloneEdge i ⊆ U then g (roleCloneEdge i) else 0) ≤
        ∑ B ∈ cloneHost G U, g B := by
  classical
  let S := (univ : Finset (EligibleRoleCoordinate markers G)).filter (fun i => roleCloneEdge i ⊆ U)
  have hs : S.image roleCloneEdge ⊆ cloneHost G U := by
    intro B hB
    obtain ⟨i,hi,rfl⟩ := mem_image.mp hB
    exact (roleCloneEdge_mem_host_iff U i).mpr (mem_filter.mp hi).2
  calc
    _ = ∑ i ∈ S, g (roleCloneEdge i) := by simp [S, sum_filter]
    _ = ∑ B ∈ S.image roleCloneEdge, g B :=
      (sum_image (fun _ _ _ _ h => roleCloneEdge_injective h)).symm
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg hs (fun B hB _ => hg B hB)

end LooseHamilton
