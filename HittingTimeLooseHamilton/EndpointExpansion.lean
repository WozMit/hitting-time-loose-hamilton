module

public import HittingTimeLooseHamilton.EndpointExpansionIndex

public section

/-! A modular cycle insertion constructor.  It derives the global cycle axioms
from local inserted junctions and private blocks disjoint from the old cycle. -/
noncomputable section
open Finset
namespace LooseHamilton.MixedCycleOnWitness
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {r : ℕ} {S : Finset V} {M E : Finset (Finset V)}

@[expose] def insertedPrivate (C : MixedCycleOnWitness r S M E) {b : ℕ}
    {E' : Finset (Finset V)} (e : (↥E ⊕ Fin b) ≃ ↥E')
    (B : Fin b → Finset V) : ↥E' → Finset V :=
  Sum.elim C.privateBlock B ∘ e.symm

@[simp] theorem insertedPrivate_old (C : MixedCycleOnWitness r S M E) {b : ℕ}
    {E' : Finset (Finset V)} (e : (↥E ⊕ Fin b) ≃ ↥E')
    (B : Fin b → Finset V) (f : ↥E) :
    C.insertedPrivate e B (e (.inl f)) = C.privateBlock f := by
  simp [insertedPrivate]

@[simp] theorem insertedPrivate_new (C : MixedCycleOnWitness r S M E) {b : ℕ}
    {E' : Finset (Finset V)} (e : (↥E ⊕ Fin b) ≃ ↥E')
    (B : Fin b → Finset V) (i : Fin b) :
    C.insertedPrivate e B (e (.inr i)) = B i := by
  simp [insertedPrivate]

theorem insertedPrivate_biUnion (C : MixedCycleOnWitness r S M E) {b : ℕ}
    {E' : Finset (Finset V)} (e : (↥E ⊕ Fin b) ≃ ↥E')
    (B : Fin b → Finset V) :
    univ.biUnion (C.insertedPrivate e B) =
      univ.biUnion C.privateBlock ∪ univ.biUnion B := by
  ext v
  simp only [mem_biUnion, mem_univ, true_and, mem_union]
  constructor
  · rintro ⟨f,hf⟩
    obtain ⟨j,rfl⟩ := e.surjective f
    cases j with
    | inl f => exact Or.inl ⟨f, by simpa using hf⟩
    | inr i => exact Or.inr ⟨i, by simpa using hf⟩
  · rintro (⟨f,hf⟩ | ⟨i,hi⟩)
    · exact ⟨e (.inl f), by simpa using hf⟩
    · exact ⟨e (.inr i), by simpa using hi⟩

/-- Insert a path at the initial slot. The slot equivalence and its local edge
identities describe the path; all global disjointness and covering axioms follow
from freshness relative to the old active set. -/
@[expose] def insertPath (C : MixedCycleOnWitness r S M E)
    {k b : ℕ} {M' E' : Finset (Finset V)}
    (A : Fin k → V) (B : Fin b → Finset V)
    (hA : Function.Injective A)
    (hAS : ∀ i, A i ∉ S)
    (hB : ∀ i, (B i).card = r - 2)
    (hBB : Pairwise (fun i j => Disjoint (B i) (B j)))
    (hBS : ∀ i, Disjoint S (B i))
    (hAB : ∀ i j, A i ∉ B j)
    (edgeEquiv : (↥E ⊕ Fin b) ≃ ↥E')
    (slotEquiv : Fin (C.length+k) ≃ (↥M' ⊕ ↥E'))
    (hM : (M' : Set (Finset V)).PairwiseDisjoint id)
    (hslot : ∀ i, match slotEquiv i with
      | .inl e => e.val =
          {endpointInsertedJunction (by have := C.length_ge; omega) C.junction A i,
          endpointInsertedJunction (by have := C.length_ge; omega) C.junction A
            (finRotate (C.length+k) i)}
      | .inr e => e.val =
          {endpointInsertedJunction (by have := C.length_ge; omega) C.junction A i,
          endpointInsertedJunction (by have := C.length_ge; omega) C.junction A
            (finRotate (C.length+k) i)} ∪ C.insertedPrivate edgeEquiv B e) :
    MixedCycleOnWitness r (S ∪ univ.image A ∪ univ.biUnion B) M' E' := by
  let J := endpointInsertedJunction (by have := C.length_ge; omega) C.junction A
  have hj : Function.Injective J := endpointInsertedJunction_injective _
    C.junction_injective hA (fun i j he => hAS j (he ▸ C.junction_mem i))
  refine {
    length := C.length+k
    length_ge := by have := C.length_ge; omega
    junction := J
    junction_injective := hj
    junction_next_ne := ?_
    slot := slotEquiv
    privateBlock := C.insertedPrivate edgeEquiv B
    private_card := ?_
    private_disjoint := ?_
    junction_private_disjoint := ?_
    cover := ?_
    marked_matching := hM
    slot_edge := hslot }
  · intro i hi
    have he := congrArg Fin.val (hj hi)
    rw [finRotate_val_eq _ (by have := C.length_ge; omega)] at he
    have hn := C.length_ge
    split_ifs at he <;> omega
  · intro e
    obtain ⟨f,rfl⟩ := edgeEquiv.surjective e
    cases f with
    | inl f => simpa using C.private_card f
    | inr j => simpa using hB j
  · intro e f hef
    obtain ⟨e,rfl⟩ := edgeEquiv.surjective e
    obtain ⟨f,rfl⟩ := edgeEquiv.surjective f
    cases e with
    | inl e =>
      cases f with
      | inl f =>
        simpa using C.private_disjoint (show e ≠ f from fun he => hef (by rw [he]))
      | inr j =>
        simpa using (hBS j).mono_left (C.private_subset_active e)
    | inr i =>
      cases f with
      | inl f =>
        simpa using ((hBS i).mono_left (C.private_subset_active f)).symm
      | inr j => simpa using hBB (show i ≠ j from fun he => hef (by rw [he]))
  · intro e
    rw [show univ.image J = univ.image C.junction ∪ univ.image A from
      endpointInsertedJunction_image _ _ _]
    obtain ⟨e,rfl⟩ := edgeEquiv.surjective e
    cases e with
    | inl e =>
      simp only [insertedPrivate_old, disjoint_union_left]
      refine ⟨C.junction_private_disjoint e, ?_⟩
      apply disjoint_left.mpr
      intro v hv hb
      obtain ⟨i,_,rfl⟩ := mem_image.mp hv
      exact hAS i (C.private_subset_active e hb)
    | inr i =>
      simp only [insertedPrivate_new, disjoint_union_left]
      constructor
      · apply (hBS i).mono_left
        intro v hv
        obtain ⟨j,_,rfl⟩ := mem_image.mp hv
        exact C.junction_mem j
      · apply disjoint_left.mpr
        intro v hv hb
        obtain ⟨j,_,rfl⟩ := mem_image.mp hv
        exact hAB j i hb
  · rw [insertedPrivate_biUnion, show univ.image J =
      univ.image C.junction ∪ univ.image A from endpointInsertedJunction_image _ _ _]
    conv_lhs => rw [C.cover]
    ext v
    simp only [mem_union]
    tauto
end LooseHamilton.MixedCycleOnWitness
