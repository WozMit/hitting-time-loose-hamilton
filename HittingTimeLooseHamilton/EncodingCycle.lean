module

public import HittingTimeLooseHamilton.Cycles

public section
noncomputable section
open Finset
namespace LooseHamilton
variable {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]
/-- Labelled slot data, before deriving the ordinary edge sets. -/
structure ExpandedCycleData (r : ℕ) (markers : Finset (Finset V)) (I : Type*)
    [Fintype I] where
  length : ℕ
  length_ge : 3 ≤ length
  junction : Fin length → V
  junction_injective : Function.Injective junction
  junction_next_ne : ∀ i, junction i ≠ junction (finRotate length i)
  slot : Fin length ≃ ({e // e ∈ markers} ⊕ I)
  privateBlock : I → Finset V
  private_card : ∀ e, (privateBlock e).card = r - 2
  private_disjoint : Pairwise (fun e f => Disjoint (privateBlock e) (privateBlock f))
  junction_private_disjoint : ∀ e, Disjoint (univ.image junction) (privateBlock e)
  cover : univ = univ.image junction ∪ univ.biUnion privateBlock
  marked_matching : (markers : Set (Finset V)).PairwiseDisjoint id
  marked_edge : ∀ e, e.val = {junction (slot.symm (Sum.inl e)),
    junction (finRotate length (slot.symm (Sum.inl e)))}
namespace ExpandedCycleData
variable {r : ℕ} {markers : Finset (Finset V)}
@[expose] def edge (D : ExpandedCycleData r markers I) (i : I) : Finset V :=
  {D.junction (D.slot.symm (.inr i)),
    D.junction (finRotate D.length (D.slot.symm (.inr i)))} ∪ D.privateBlock i
@[expose] def edges (D : ExpandedCycleData r markers I) : Finset (Finset V) := univ.image D.edge

omit [DecidableEq I] in
theorem edge_injective (D : ExpandedCycleData r markers I) (hr : 3 ≤ r) :
    Function.Injective D.edge := by
  intro i j hij
  by_contra hne
  have hp : (D.privateBlock i).Nonempty := by
    rw [← card_pos, D.private_card]
    omega
  obtain ⟨v, hv⟩ := hp
  have hj : v ∈ D.edge j := by
    rw [← hij]
    exact mem_union_right _ hv
  rcases mem_union.mp hj with hj | hj
  · have hJ : v ∈ univ.image D.junction := by
      simp only [mem_insert, mem_singleton] at hj
      rcases hj with rfl | rfl <;> exact mem_image_of_mem _ (mem_univ _)
    exact disjoint_left.mp (D.junction_private_disjoint i) hJ hv
  · exact disjoint_left.mp (D.private_disjoint hne) hv hj

@[expose] def edgeEquiv (D : ExpandedCycleData r markers I) (hr : 3 ≤ r) :
    I ≃ {e // e ∈ D.edges} := Equiv.ofBijective
  (fun i => ⟨D.edge i, mem_image_of_mem _ (mem_univ _)⟩) (by
    constructor
    · intro i j h
      exact D.edge_injective hr (congrArg Subtype.val h)
    · rintro ⟨e, he⟩
      obtain ⟨i, _, rfl⟩ := mem_image.mp he
      exact ⟨i, rfl⟩)
@[simp] theorem edgeEquiv_val (D : ExpandedCycleData r markers I) (hr : 3 ≤ r) (i : I) :
    (D.edgeEquiv hr i).val = D.edge i := rfl
@[simp] theorem edge_equiv_symm (D : ExpandedCycleData r markers I) (hr : 3 ≤ r)
    (e : {e // e ∈ D.edges}) : D.edge ((D.edgeEquiv hr).symm e) = e.val := by
  exact congrArg Subtype.val ((D.edgeEquiv hr).apply_symm_apply e)
/-- Forget labels and retain the actual unoriented edge sets. -/
@[expose] def witness (D : ExpandedCycleData r markers I) (hr : 3 ≤ r) :
    MixedCycleWitness r markers D.edges where
  length := D.length
  length_ge := D.length_ge
  junction := D.junction
  junction_injective := D.junction_injective
  junction_next_ne := D.junction_next_ne
  slot := D.slot.trans (Equiv.sumCongr (Equiv.refl _) (D.edgeEquiv hr))
  privateBlock := fun e => D.privateBlock ((D.edgeEquiv hr).symm e)
  private_card := fun e => D.private_card _
  private_disjoint := by
    intro e f hef
    exact D.private_disjoint (fun h => hef ((D.edgeEquiv hr).symm.injective h))
  junction_private_disjoint := fun e => D.junction_private_disjoint _
  cover := by
    rw [D.cover]
    congr 1
    ext v
    simp only [mem_biUnion, mem_univ, true_and]
    constructor
    · rintro ⟨i, hi⟩
      exact ⟨D.edgeEquiv hr i, by simpa using hi⟩
    · rintro ⟨e, he⟩
      exact ⟨(D.edgeEquiv hr).symm e, he⟩
  marked_matching := D.marked_matching
  slot_edge := by
    intro i
    cases hs : D.slot i with
    | inl e =>
      have hi : D.slot.symm (.inl e) = i := by rw [← hs]; simp
      simpa [Equiv.trans_apply, hs, hi] using D.marked_edge e
    | inr e =>
      have hi : D.slot.symm (.inr e) = i := by rw [← hs]; simp
      simp [Equiv.trans_apply, hs, edge, hi]
theorem isMixedCycle (D : ExpandedCycleData r markers I) (hr : 3 ≤ r) :
    IsMixedCycle r markers D.edges := ⟨D.witness hr⟩
theorem edges_card (D : ExpandedCycleData r markers I) (hr : 3 ≤ r) :
    D.edges.card = Fintype.card I := by
  simpa using (Fintype.card_congr (D.edgeEquiv hr)).symm
end ExpandedCycleData
end LooseHamilton
