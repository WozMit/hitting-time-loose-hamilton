module

public import HittingTimeLooseHamilton.EncodingCycle
public import HittingTimeLooseHamilton.CyclicTraversal

public section
noncomputable section
open Finset
namespace LooseHamilton
variable {V A I : Type*} [Fintype V] [DecidableEq V]
  [Fintype A] [DecidableEq A] [Fintype I] [DecidableEq I]
/-- A cycle on labelled junctions; this is independent of any choice of finite traversal. -/
structure PermutationCycleData (r : ℕ) (markers : Finset (Finset V)) (A I : Type*)
    [Fintype A] [Fintype I] where
  card_ge : 3 ≤ Fintype.card A
  successor : Equiv.Perm A
  cyclic : successor.IsCycleOn Set.univ
  root : A
  junction : A ↪ V
  slot : A ≃ ({e // e ∈ markers} ⊕ I)
  privateBlock : I → Finset V
  private_card : ∀ e, (privateBlock e).card = r - 2
  private_disjoint : Pairwise (fun e f => Disjoint (privateBlock e) (privateBlock f))
  junction_private_disjoint : ∀ e, Disjoint (univ.image junction) (privateBlock e)
  cover : univ = univ.image junction ∪ univ.biUnion privateBlock
  marked_matching : (markers : Set (Finset V)).PairwiseDisjoint id
  marked_edge : ∀ e, e.val = {junction (slot.symm (Sum.inl e)),
    junction (successor (slot.symm (Sum.inl e)))}
namespace PermutationCycleData
variable {r : ℕ} {markers : Finset (Finset V)}
@[expose] def expanded (D : PermutationCycleData r markers A I) : ExpandedCycleData r markers I := by
  let t := BlockEnumeration.cycleTraversal D.successor D.cyclic D.root
  have ht (i) : t (finRotate _ i) = D.successor (t i) :=
    BlockEnumeration.cycleTraversal_rotate _ _ _ _
  have himage : univ.image (fun i => D.junction (t i)) = univ.image D.junction := by
    ext v
    simp only [mem_image, mem_univ, true_and]
    constructor
    · rintro ⟨i, rfl⟩; exact ⟨t i, rfl⟩
    · rintro ⟨a, rfl⟩; exact ⟨t.symm a, by simp⟩
  refine {
    length := Fintype.card A
    length_ge := D.card_ge
    junction := fun i => D.junction (t i)
    junction_injective := D.junction.injective.comp t.injective
    junction_next_ne := ?_
    slot := t.trans D.slot
    privateBlock := D.privateBlock
    private_card := D.private_card
    private_disjoint := D.private_disjoint
    junction_private_disjoint := ?_
    cover := ?_
    marked_matching := D.marked_matching
    marked_edge := ?_ }
  · intro i hi
    have ha := D.junction.injective hi
    rw [ht] at ha
    have hnt : (Set.univ : Set A).Nontrivial := by
      rw [Set.nontrivial_univ_iff]
      exact Fintype.one_lt_card_iff_nontrivial.mp (by have := D.card_ge; omega)
    exact D.cyclic.apply_ne hnt (Set.mem_univ _) ha.symm
  · intro e
    rw [himage]
    exact D.junction_private_disjoint e
  · rw [himage]
    exact D.cover
  · intro e
    change e.val = {D.junction (t (t.symm (D.slot.symm (.inl e)))), D.junction (t (finRotate _ (t.symm (D.slot.symm (.inl e)))))} 
    rw [ht]
    simpa using D.marked_edge e

@[expose] def witness (D : PermutationCycleData r markers A I) (hr : 3 ≤ r) := D.expanded.witness hr

theorem isMixedCycle (D : PermutationCycleData r markers A I) (hr : 3 ≤ r) :
    IsMixedCycle r markers D.expanded.edges := D.expanded.isMixedCycle hr

theorem expanded_junction_image (D : PermutationCycleData r markers A I) :
    univ.image D.expanded.junction = univ.image D.junction := by
  ext v
  constructor
  · intro hv
    obtain ⟨i, _, hi⟩ := mem_image.mp hv
    exact mem_image.mpr ⟨BlockEnumeration.cycleTraversal D.successor D.cyclic D.root i,
      mem_univ _, hi⟩
  · intro hv
    obtain ⟨a, _, rfl⟩ := mem_image.mp hv
    refine mem_image.mpr ⟨(BlockEnumeration.cycleTraversal D.successor D.cyclic D.root).symm a,
      mem_univ _, ?_⟩
    exact congrArg D.junction ((BlockEnumeration.cycleTraversal D.successor D.cyclic D.root).apply_symm_apply a)


theorem expanded_edge (D : PermutationCycleData r markers A I) (i : I) :
    D.expanded.edge i =
      {D.junction (D.slot.symm (.inr i)), D.junction (D.successor (D.slot.symm (.inr i)))} ∪
        D.privateBlock i := by
  let t := BlockEnumeration.cycleTraversal D.successor D.cyclic D.root
  change {D.junction (t (t.symm (D.slot.symm (.inr i)))),
    D.junction (t (finRotate _ (t.symm (D.slot.symm (.inr i)))))} ∪ _ = _
  rw [BlockEnumeration.cycleTraversal_rotate]
  dsimp only [t]
  simp only [Equiv.apply_symm_apply]
  rfl

theorem expanded_marker_start (D : PermutationCycleData r markers A I) (e : ↥markers) :
    D.expanded.junction (D.expanded.slot.symm (.inl e)) = D.junction (D.slot.symm (.inl e)) := by
  change D.junction ((BlockEnumeration.cycleTraversal D.successor D.cyclic D.root)
    ((BlockEnumeration.cycleTraversal D.successor D.cyclic D.root).symm
      (D.slot.symm (.inl e)))) = _
  rw [Equiv.apply_symm_apply]
end PermutationCycleData
end LooseHamilton
