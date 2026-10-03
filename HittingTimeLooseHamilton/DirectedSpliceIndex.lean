module

public import HittingTimeLooseHamilton.EndpointIndex

public section

namespace LooseHamilton
/-- Reverse a closed interval of cyclic indices, leaving its complement fixed. -/
@[expose] def spliceReflect {n : ℕ} (lo hi : ℕ) (hh : hi < n) (i : Fin n) : Fin n :=
  ⟨if lo ≤ i.val ∧ i.val ≤ hi then lo + hi - i.val else i.val, by
    split_ifs with h <;> omega⟩

@[simp] theorem spliceReflect_val {n : ℕ} (lo hi : ℕ) (hh : hi < n) (i : Fin n) :
    (spliceReflect lo hi hh i).val =
      if lo ≤ i.val ∧ i.val ≤ hi then lo + hi - i.val else i.val := rfl

theorem spliceReflect_involutive {n : ℕ} (lo hi : ℕ) (hh : hi < n) :
    Function.Involutive (spliceReflect lo hi hh) := by
  intro i
  apply Fin.ext
  simp only [spliceReflect_val]
  split_ifs <;> omega

@[expose] def spliceReflectEquiv {n : ℕ} (lo hi : ℕ) (hh : hi < n) : Equiv.Perm (Fin n) :=
  ⟨spliceReflect lo hi hh, spliceReflect lo hi hh,
    spliceReflect_involutive lo hi hh, spliceReflect_involutive lo hi hh⟩

/-- Junctions in positions `1,...,j` are reversed. -/
@[expose] def spliceJunctionIndex {n : ℕ} (j : Fin n) : Equiv.Perm (Fin n) :=
  spliceReflectEquiv 1 j.val j.isLt

/-- Slots strictly between the two cut markers are reversed. -/
@[expose] def spliceSlotIndex {n : ℕ} (j : Fin n) : Equiv.Perm (Fin n) :=
  spliceReflectEquiv 1 (j.val-1) (by omega)

@[simp] theorem spliceJunctionIndex_val {n : ℕ} (j i : Fin n) :
    (spliceJunctionIndex j i).val =
      if 1 ≤ i.val ∧ i.val ≤ j.val then 1+j.val-i.val else i.val := rfl
@[simp] theorem spliceSlotIndex_val {n : ℕ} (j i : Fin n) :
    (spliceSlotIndex j i).val =
      if 1 ≤ i.val ∧ i.val ≤ j.val-1 then 1+(j.val-1)-i.val else i.val := rfl

theorem splice_indices_internal {n : ℕ} (j i : Fin n)
    (hi : 0 < i.val) (hij : i.val < j.val) :
    spliceJunctionIndex j i = finRotate n (spliceSlotIndex j i) ∧
    spliceJunctionIndex j (finRotate n i) = spliceSlotIndex j i := by
  have hn : 0 < n := by omega
  constructor <;> apply Fin.ext <;>
    simp only [spliceJunctionIndex_val, spliceSlotIndex_val, finRotate_val_eq n hn] <;>
    split_ifs <;> omega

theorem splice_indices_external {n : ℕ} (j i : Fin n)
    (hj : 0 < j.val) (hi : j.val < i.val) :
    spliceJunctionIndex j i = spliceSlotIndex j i ∧
    spliceJunctionIndex j (finRotate n i) = finRotate n (spliceSlotIndex j i) := by
  have hn : 0 < n := by omega
  constructor <;> apply Fin.ext <;>
    simp only [spliceJunctionIndex_val, spliceSlotIndex_val, finRotate_val_eq n hn] <;>
    split_ifs <;> omega

@[simp] theorem spliceJunctionIndex_zero {n : ℕ} (j : Fin n) (hn : 0 < n) :
    spliceJunctionIndex j ⟨0,hn⟩ = ⟨0,hn⟩ := by
  apply Fin.ext; simp
@[simp] theorem spliceSlotIndex_zero {n : ℕ} (j : Fin n) (hn : 0 < n) :
    spliceSlotIndex j ⟨0,hn⟩ = ⟨0,hn⟩ := by
  apply Fin.ext; simp
@[simp] theorem spliceSlotIndex_cut {n : ℕ} (j : Fin n) :
    spliceSlotIndex j j = j := by
  apply Fin.ext; simp only [spliceSlotIndex_val]; split_ifs <;> omega

theorem spliceJunctionIndex_one {n : ℕ} (j : Fin n) (hj : 0 < j.val) :
    spliceJunctionIndex j ⟨1,by omega⟩ = j := by
  apply Fin.ext; simp only [spliceJunctionIndex_val]; split_ifs <;> omega

theorem spliceJunctionIndex_cut {n : ℕ} (j : Fin n) (hj : 0 < j.val) :
    spliceJunctionIndex j j = ⟨1,by omega⟩ := by
  apply Fin.ext; simp only [spliceJunctionIndex_val]; split_ifs <;> omega

theorem spliceJunctionIndex_cut_next {n : ℕ} (j : Fin n) (hj : 0 < j.val) :
    spliceJunctionIndex j (finRotate n j) = finRotate n j := by
  apply Fin.ext
  simp only [spliceJunctionIndex_val, finRotate_val_eq n (by omega)]
  split_ifs <;> omega
end LooseHamilton
