module

public import HittingTimeLooseHamilton.EndpointIndex

public section

/-! Cyclic index insertion, inverse to deleting the interior of an initial path. -/
namespace LooseHamilton

@[expose] def endpointInsertIndex (m k : ℕ) (hm : 0 < m) : Fin m ⊕ Fin k → Fin (m+k)
  | .inl i => endpointKeep m k i
  | .inr j => ⟨j.val+1, by omega⟩

theorem endpointInsertIndex_bijective {m k : ℕ} (hm : 0 < m) :
    Function.Bijective (endpointInsertIndex m k hm) := by
  constructor
  · intro a b h
    cases a with
    | inl a =>
      cases b with
      | inl b => exact congrArg Sum.inl (endpointKeep_injective m k h)
      | inr b =>
        have hv := congrArg Fin.val h
        simp only [endpointInsertIndex, endpointKeep_val] at hv
        split_ifs at hv <;> omega
    | inr a =>
      cases b with
      | inl b =>
        have hv := congrArg Fin.val h
        simp only [endpointInsertIndex, endpointKeep_val] at hv
        split_ifs at hv <;> omega
      | inr b =>
        have hv := congrArg Fin.val h
        simp only [endpointInsertIndex] at hv
        exact congrArg Sum.inr (Fin.ext (by omega))
  · intro j
    by_cases hj : j.val = 0 ∨ k < j.val
    · obtain ⟨i, hi⟩ := (mem_range_endpointKeep hm j).mpr hj
      exact ⟨.inl i, hi⟩
    · exact ⟨.inr ⟨j.val-1, by omega⟩, Fin.ext (by simp [endpointInsertIndex]; omega)⟩

@[expose] noncomputable def endpointInsertEquiv (m k : ℕ) (hm : 0 < m) :
    (Fin m ⊕ Fin k) ≃ Fin (m+k) :=
  Equiv.ofBijective (endpointInsertIndex m k hm) (endpointInsertIndex_bijective hm)

@[simp] theorem endpointInsertEquiv_inl (m k : ℕ) (hm : 0 < m) (i : Fin m) :
    endpointInsertEquiv m k hm (.inl i) = endpointKeep m k i := rfl

@[simp] theorem endpointInsertEquiv_inr (m k : ℕ) (hm : 0 < m) (i : Fin k) :
    endpointInsertEquiv m k hm (.inr i) = ⟨i.val+1, by omega⟩ := rfl

@[expose] noncomputable def endpointInsertedJunction {V : Type*} {m k : ℕ} (hm : 0 < m)
    (old : Fin m → V) (added : Fin k → V) : Fin (m+k) → V :=
  Sum.elim old added ∘ (endpointInsertEquiv m k hm).symm

@[simp] theorem endpointInsertedJunction_old {V : Type*} {m k : ℕ} (hm : 0 < m)
    (old : Fin m → V) (added : Fin k → V) (i : Fin m) :
    endpointInsertedJunction hm old added (endpointKeep m k i) = old i := by
  change Sum.elim old added ((endpointInsertEquiv m k hm).symm
    (endpointInsertEquiv m k hm (.inl i))) = _
  rw [Equiv.symm_apply_apply]
  rfl

@[simp] theorem endpointInsertedJunction_added {V : Type*} {m k : ℕ} (hm : 0 < m)
    (old : Fin m → V) (added : Fin k → V) (j : Fin k) :
    endpointInsertedJunction hm old added ⟨j.val+1, by omega⟩ = added j := by
  change Sum.elim old added ((endpointInsertEquiv m k hm).symm
    (endpointInsertEquiv m k hm (.inr j))) = _
  rw [Equiv.symm_apply_apply]
  rfl

theorem endpointInsertedJunction_injective {V : Type*} {m k : ℕ} (hm : 0 < m)
    {old : Fin m → V} {added : Fin k → V} (ho : Function.Injective old)
    (ha : Function.Injective added) (hd : ∀ i j, old i ≠ added j) :
    Function.Injective (endpointInsertedJunction hm old added) := by
  apply Function.Injective.comp _ (endpointInsertEquiv m k hm).symm.injective
  intro a b h
  cases a with
  | inl a =>
    cases b with
    | inl b => exact congrArg Sum.inl (ho h)
    | inr b => exact False.elim (hd a b h)
  | inr a =>
    cases b with
    | inl b => exact False.elim (hd b a h.symm)
    | inr b => exact congrArg Sum.inr (ha h)

open Finset in
theorem endpointInsertedJunction_image {V : Type*} [DecidableEq V]
    {m k : ℕ} (hm : 0 < m) (old : Fin m → V) (added : Fin k → V) :
    univ.image (endpointInsertedJunction hm old added) =
      univ.image old ∪ univ.image added := by
  ext v
  simp only [mem_image, mem_univ, true_and, mem_union]
  constructor
  · rintro ⟨i, rfl⟩
    obtain ⟨j, rfl⟩ := (endpointInsertEquiv m k hm).surjective i
    cases j with
    | inl j => exact Or.inl ⟨j, by simp⟩
    | inr j => exact Or.inr ⟨j, by simp⟩
  · rintro (⟨i, rfl⟩ | ⟨i, rfl⟩)
    · exact ⟨endpointKeep m k i, by simp⟩
    · exact ⟨⟨i.val+1, by omega⟩, by simp⟩

theorem endpointInsertedJunction_zero {V : Type*} {m k : ℕ} (hm : 0 < m)
    (old : Fin m → V) (added : Fin k → V) :
    endpointInsertedJunction hm old added ⟨0, by omega⟩ = old ⟨0, hm⟩ := by
  have h := endpointInsertedJunction_old hm old added ⟨0,hm⟩
  exact h

theorem endpointInsertedJunction_first_next {V : Type*} {m k : ℕ}
    (hm : 2 ≤ m) (hk : 0 < k) (old : Fin m → V) (added : Fin k → V) :
    endpointInsertedJunction (by omega) old added
      (finRotate (m+k) ⟨0,by omega⟩) = added ⟨0,hk⟩ := by
  have he : finRotate (m+k) ⟨0,by omega⟩ = (⟨1,by omega⟩ : Fin (m+k)) := by
    apply Fin.ext
    simp only [finRotate_val_eq, show 0 < m+k by omega, show 1 < m+k by omega, ↓reduceIte]
  rw [he]
  exact endpointInsertedJunction_added _ _ _ ⟨0,hk⟩

theorem endpointInsertedJunction_last_next {V : Type*} {m k : ℕ}
    (hm : 2 ≤ m) (old : Fin m → V) (added : Fin k → V) :
    endpointInsertedJunction (by omega) old added
      (finRotate (m+k) ⟨k,by omega⟩) = old ⟨1,by omega⟩ := by
  have he : finRotate (m+k) ⟨k,by omega⟩ = endpointKeep m k ⟨1,by omega⟩ := by
    apply Fin.ext
    simp only [finRotate_val_eq, show 0 < m+k by omega, show k+1 < m+k by omega,
      endpointKeep, Nat.add_comm]
    <;> simp_all <;> omega
  rw [he, endpointInsertedJunction_old]
end LooseHamilton
