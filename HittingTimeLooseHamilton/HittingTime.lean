module

public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Finset.Range

public section

/-! # Finite process hitting times

The value `⊤` means the property never occurs in the finite process, so the
empty hitting set is not assigned a spurious finite stopping time.
-/
namespace LooseHamilton
noncomputable section

variable {State : Type*}

/-- First time in `0,...,K` at which `P` holds along `H`, or infinity. -/
@[expose] def firstTime (K : ℕ) (H : ℕ → State) (P : State → Prop) : WithTop ℕ := by
  classical
  exact ((Finset.range (K + 1)).filter fun t => P (H t)).min

/-- A stronger property cannot be reached before a weaker one. -/
theorem firstTime_le_of_imp (K : ℕ) (H : ℕ → State) {P Q : State → Prop}
    (h : ∀ t ≤ K, P (H t) → Q (H t)) :
    firstTime K H Q ≤ firstTime K H P := by
  classical
  apply Finset.min_mono
  intro t ht
  obtain ⟨ht, hp⟩ := Finset.mem_filter.mp ht
  exact Finset.mem_filter.mpr ⟨ht, h t (Nat.le_of_lt_succ (Finset.mem_range.mp ht)) hp⟩

/-- If a property holds at a time in the process, its hitting time is no later. -/
theorem firstTime_le (K : ℕ) (H : ℕ → State) (P : State → Prop)
    {t : ℕ} (ht : t ≤ K) (hp : P (H t)) : firstTime K H P ≤ t := by
  classical
  exact Finset.min_le (Finset.mem_filter.mpr
    ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le ht), hp⟩)

/-- A finite hitting time belongs to the time horizon and has the property. -/
theorem firstTime_spec (K : ℕ) (H : ℕ → State) (P : State → Prop)
    {t : ℕ} (h : firstTime K H P = t) : t ≤ K ∧ P (H t) := by
  classical
  obtain ⟨ht, hp⟩ := Finset.mem_filter.mp (Finset.mem_of_min h)
  exact ⟨Nat.le_of_lt_succ (Finset.mem_range.mp ht), hp⟩

/-- Every earlier time fails the property. -/
theorem not_before_firstTime (K : ℕ) (H : ℕ → State) (P : State → Prop)
    {t : ℕ} (ht : t ≤ K) (h : (t : WithTop ℕ) < firstTime K H P) : ¬ P (H t) := by
  intro hp
  exact (not_le_of_gt h) (firstTime_le K H P ht hp)

/-- Infinity is returned exactly when no time in the process has the property. -/
theorem firstTime_eq_top (K : ℕ) (H : ℕ → State) (P : State → Prop) :
    firstTime K H P = ⊤ ↔ ∀ t ≤ K, ¬ P (H t) := by
  classical
  simp only [firstTime, Finset.min_eq_top, Finset.eq_empty_iff_forall_notMem,
    Finset.mem_filter, Finset.mem_range, not_and]
  simp only [Nat.lt_succ_iff]

end
end LooseHamilton
