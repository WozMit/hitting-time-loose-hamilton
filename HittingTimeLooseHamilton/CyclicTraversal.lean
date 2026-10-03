module

public import HittingTimeLooseHamilton.GapPermutation
public import Mathlib.GroupTheory.Perm.Fin

public section

namespace LooseHamilton.BlockEnumeration

variable {A : Type*} [Fintype A]

/-- Traverse a full cyclic permutation from the prescribed root. -/
@[expose] noncomputable def cycleTraversal (σ : Equiv.Perm A) (hσ : σ.IsCycleOn Set.univ) (a : A) :
    Fin (Fintype.card A) ≃ A :=
  Equiv.ofBijective (fun i => (σ ^ (i : ℕ)) a) (by
    classical
    have hs : σ.IsCycleOn (Finset.univ : Finset A) := by simpa using hσ
    constructor
    · intro i j hij
      apply Fin.ext
      have h := (hs.pow_apply_eq_pow_apply (Finset.mem_univ a)).mp hij
      change i.val % (Finset.univ : Finset A).card = j.val % (Finset.univ : Finset A).card at h
      simpa only [Finset.card_univ, Nat.mod_eq_of_lt i.isLt, Nat.mod_eq_of_lt j.isLt] using h
    · intro b
      obtain ⟨n, hn, he⟩ := hs.exists_pow_eq (Finset.mem_univ a) (Finset.mem_univ b)
      exact ⟨⟨n, by simpa using hn⟩, he⟩)

@[simp] theorem cycleTraversal_apply (σ : Equiv.Perm A) (hσ : σ.IsCycleOn Set.univ)
    (a : A) (i : Fin (Fintype.card A)) : cycleTraversal σ hσ a i = (σ ^ i.val) a := rfl

@[simp] theorem cycleTraversal_zero (σ : Equiv.Perm A) (hσ : σ.IsCycleOn Set.univ)
    (a : A) (h : 0 < Fintype.card A) : cycleTraversal σ hσ a ⟨0, h⟩ = a := rfl

/-- Traversal takes cyclically successive positions to successive vertices. -/
theorem cycleTraversal_rotate (σ : Equiv.Perm A) (hσ : σ.IsCycleOn Set.univ)
    (a : A) (i : Fin (Fintype.card A)) :
    cycleTraversal σ hσ a (finRotate _ i) = σ (cycleTraversal σ hσ a i) := by
  classical
  have hn : 0 < Fintype.card A := Fintype.card_pos_iff.mpr ⟨a⟩
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  have hs : σ.IsCycleOn (Finset.univ : Finset A) := by simpa using hσ
  simp only [cycleTraversal_apply]
  have hh : ∀ i : Fin (n + 1),
      (σ ^ (finRotate (n + 1) i).val) a = σ ((σ ^ i.val) a) := by
    intro i
    by_cases hi : i = Fin.last n
    · subst i
      rw [finRotate_last]
      have hcard := hs.pow_card_apply (Finset.mem_univ a)
      simp only [Finset.card_univ, hn] at hcard
      simpa only [Fin.val_zero, pow_zero, Equiv.Perm.one_apply, Fin.val_last,
        pow_succ', Equiv.Perm.mul_apply] using hcard.symm
    · rw [coe_finRotate_of_ne_last hi, pow_succ', Equiv.Perm.mul_apply]
  revert i
  rw [hn]
  exact hh

end LooseHamilton.BlockEnumeration
