module

public import Mathlib.Data.Fintype.Perm
public import Mathlib.Data.Fintype.CardEmbedding
public import Mathlib.Tactic

public section

/-!
# Labelled block-order codes

Rooting a directed cyclic order at a prescribed block leaves a linear permutation of
all the other blocks. An allowed order can instead be rooted at an ordinary block:
order the remaining ordinary blocks and assign distinct ordinary gaps to the labelled
markers. Each marker is inserted immediately after the ordinary block naming its gap.

These are enumeration codes. Their cardinality statements do not by themselves identify
codes with unoriented edge sets; that identification is a separate reconstruction step.
-/
namespace LooseHamilton.BlockEnumeration

/-- Order of the nonroot labels in a rooted directed cyclic order of `k` labels. -/
abbrev RootedOrder (k : ℕ) := Equiv.Perm (Fin (k - 1))

/-- Root an ordinary block, order the other ordinary blocks, then insert each labelled
marker in its own gap. There are `k-s` ordinary blocks and hence `k-s` gaps. -/
abbrev SeparatedOrder (k s : ℕ) :=
  Equiv.Perm (Fin (k - s - 1)) × (Fin s ↪ Fin (k - s))

/-- Fixing the root marker's direction leaves one binary direction per other marker. -/
abbrev MarkerDirections (s : ℕ) := Fin (s - 1) → Bool

@[simp] theorem card_rootedOrder (k : ℕ) :
    Fintype.card (RootedOrder k) = (k - 1).factorial := by
  simp [RootedOrder, Fintype.card_perm]

@[simp] theorem card_markerDirections (s : ℕ) :
    Fintype.card (MarkerDirections s) = 2 ^ (s - 1) := by
  simp [MarkerDirections]

@[simp] theorem card_separatedOrder (k s : ℕ) :
    Fintype.card (SeparatedOrder k s) =
      (k - s - 1).factorial * (k - s).descFactorial s := by
  simp [SeparatedOrder, Fintype.card_perm]

/-- The factorial form of the count of separated-order codes. -/
theorem card_separatedOrder_factorial {k s : ℕ} (hks : 2 * s ≤ k) :
    Fintype.card (SeparatedOrder k s) =
      (k - s).factorial * (k - s - 1).factorial / (k - 2 * s).factorial := by
  rw [card_separatedOrder, Nat.descFactorial_eq_div (by omega)]
  have hsub : k - s - s = k - 2 * s := by omega
  rw [hsub, ← Nat.mul_div_assoc _ (Nat.factorial_dvd_factorial (by omega))]
  rw [Nat.mul_comm]

/-- A division-free identity, useful when passing from natural to real counts. -/
theorem card_separatedOrder_mul_factorial {k s : ℕ} (hks : 2 * s ≤ k) :
    Fintype.card (SeparatedOrder k s) * (k - 2 * s).factorial =
      (k - s).factorial * (k - s - 1).factorial := by
  rw [card_separatedOrder]
  have hsub : k - s - s = k - 2 * s := by omega
  have h := Nat.factorial_mul_descFactorial (show s ≤ k - s by omega)
  rw [hsub] at h
  calc
    (k - s - 1).factorial * (k - s).descFactorial s * (k - 2 * s).factorial =
        ((k - 2 * s).factorial * (k - s).descFactorial s) *
          (k - s - 1).factorial := by ring
    _ = _ := by rw [h]

/-- The exact allowed/unrestricted block-code ratio in the manuscript. -/
theorem separated_order_ratio {k s : ℕ} (hks : 2 * s ≤ k) :
    (Fintype.card (SeparatedOrder k s) : ℝ) / Fintype.card (RootedOrder k) =
      ((k - s).factorial : ℝ) * (k - s - 1).factorial /
        ((k - 1).factorial * (k - 2 * s).factorial) := by
  have h : (Fintype.card (SeparatedOrder k s) : ℝ) * (k - 2 * s).factorial =
      (k - s).factorial * (k - s - 1).factorial := by
    exact_mod_cast card_separatedOrder_mul_factorial hks
  rw [card_rootedOrder]
  have h₂ : ((k - 2 * s).factorial : ℝ) ≠ 0 := by positivity
  calc
    _ = ((Fintype.card (SeparatedOrder k s) : ℝ) * (k - 2 * s).factorial) /
        ((k - 1).factorial * (k - 2 * s).factorial) :=
      (mul_div_mul_right _ _ h₂).symm
    _ = _ := by rw [h]

end LooseHamilton.BlockEnumeration
