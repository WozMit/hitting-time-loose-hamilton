module

public import HittingTimeLooseHamilton.CycleOn

public section

/-! Cyclic indices for replacing a nonempty initial path by one slot. -/
namespace LooseHamilton

/-- Keep index zero and delete the next `k` junctions. -/
@[expose] def endpointKeep (m k : ℕ) (i : Fin m) : Fin (m + k) :=
  ⟨if i.val = 0 then 0 else i.val + k, by split_ifs <;> omega⟩

@[simp] theorem endpointKeep_val (m k : ℕ) (i : Fin m) :
    (endpointKeep m k i).val = if i.val = 0 then 0 else i.val + k := rfl

theorem endpointKeep_injective (m k : ℕ) : Function.Injective (endpointKeep m k) := by
  intro a b h
  have he := congrArg Fin.val h
  simp only [endpointKeep_val] at he
  apply Fin.ext
  split_ifs at he <;> omega

theorem finRotate_val_eq (m : ℕ) (hm : 0 < m) (i : Fin m) :
    (finRotate m i).val = if i.val + 1 < m then i.val + 1 else 0 := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
  rw [coe_finRotate]
  split_ifs with h h' h' <;> simp_all [Fin.ext_iff] <;> omega

/-- All slots after the replaced prefix retain their original successor. -/
theorem endpointKeep_rotate {m k : ℕ} (hm : 2 ≤ m) (i : Fin m)
    (hi : i.val ≠ 0) :
    endpointKeep m k (finRotate m i) = finRotate (m + k) (endpointKeep m k i) := by
  apply Fin.ext
  simp only [endpointKeep_val, finRotate_val_eq m (by omega),
    finRotate_val_eq (m+k) (by omega)]
  split_ifs <;> simp_all [endpointKeep_val] <;> omega

/-- The first replacement slot joins old junction zero to old junction `k+1`. -/
theorem endpointKeep_first_successor {m k : ℕ} (hm : 2 ≤ m) :
    endpointKeep m k (finRotate m ⟨0, by omega⟩) = ⟨k+1, by omega⟩ := by
  apply Fin.ext
  simp only [endpointKeep_val, finRotate_val_eq m (by omega)]
  simp [show 1 < m by omega, Nat.add_comm]

/-- The discarded junction indices form precisely the interior of the prefix. -/
theorem mem_range_endpointKeep {m k : ℕ} (hm : 0 < m) (j : Fin (m+k)) :
    (∃ i : Fin m, endpointKeep m k i = j) ↔ j.val = 0 ∨ k < j.val := by
  constructor
  · rintro ⟨i, rfl⟩
    simp only [endpointKeep_val]
    split_ifs <;> simp_all [endpointKeep_val] <;> omega
  · rintro (hj | hj)
    · exact ⟨⟨0, hm⟩, Fin.ext (by simpa using hj.symm)⟩
    · refine ⟨⟨j.val-k, by omega⟩, ?_⟩
      apply Fin.ext
      simp only [endpointKeep_val]
      split_ifs <;> omega
end LooseHamilton
