module

public import HittingTimeLooseHamilton.BlockEnumeration
public import Mathlib.GroupTheory.Perm.Cycle.Basic

public section

namespace LooseHamilton.BlockEnumeration

variable {A B : Type*}

/-- Insert a marker after the ordinary block naming its gap. -/
@[expose] noncomputable def gapNext (σ : Equiv.Perm A) (g : B ↪ A) : A ⊕ B → A ⊕ B := by
  classical
  exact Sum.elim (fun a => if h : ∃ b, g b = a then Sum.inr h.choose else Sum.inl (σ a))
    (fun b => Sum.inl (σ (g b)))

@[expose] noncomputable def gapPrev (σ : Equiv.Perm A) (g : B ↪ A) : A ⊕ B → A ⊕ B := by
  classical
  exact Sum.elim (fun a => if h : ∃ b, g b = σ.symm a then Sum.inr h.choose
    else Sum.inl (σ.symm a)) (fun b => Sum.inl (g b))

@[simp] theorem gapNext_inr (σ : Equiv.Perm A) (g : B ↪ A) (b : B) :
    gapNext σ g (.inr b) = .inl (σ (g b)) := by rfl

@[simp] theorem gapPrev_inr (σ : Equiv.Perm A) (g : B ↪ A) (b : B) :
    gapPrev σ g (.inr b) = .inl (g b) := rfl

@[simp] theorem gapNext_gap (σ : Equiv.Perm A) (g : B ↪ A) (b : B) :
    gapNext σ g (.inl (g b)) = .inr b := by
  classical
  simp only [gapNext, Sum.elim_inl]
  split_ifs with h
  · congr 1
    exact g.injective h.choose_spec
  · exact (h ⟨b, rfl⟩).elim

@[simp] theorem gapPrev_gap (σ : Equiv.Perm A) (g : B ↪ A) (b : B) :
    gapPrev σ g (.inl (σ (g b))) = .inr b := by
  classical
  simp only [gapPrev, Sum.elim_inl, Equiv.symm_apply_apply]
  split_ifs with h
  · congr 1
    exact g.injective h.choose_spec
  · exact (h ⟨b, rfl⟩).elim

/-- The successor permutation on ordinary blocks and inserted markers. -/
@[expose] noncomputable def gapPermutation (σ : Equiv.Perm A) (g : B ↪ A) : Equiv.Perm (A ⊕ B) where
  toFun := gapNext σ g
  invFun := gapPrev σ g
  left_inv := by
    classical
    intro x
    cases x with
    | inr b => simp
    | inl a =>
      change gapPrev σ g (if h : ∃ b, g b = a then .inr h.choose else .inl (σ a)) = _
      split_ifs with h
      · simpa using congrArg (Sum.inl : A → A ⊕ B) h.choose_spec
      · simp only [gapPrev, Sum.elim_inl, Equiv.symm_apply_apply, dif_neg h]
  right_inv := by
    classical
    intro x
    cases x with
    | inr b => simp
    | inl a =>
      change gapNext σ g (if h : ∃ b, g b = σ.symm a then .inr h.choose
        else .inl (σ.symm a)) = _
      split_ifs with h
      · simp only [gapNext_inr, h.choose_spec, Equiv.apply_symm_apply]
      · simp only [gapNext, Sum.elim_inl, dif_neg h, Equiv.apply_symm_apply]

@[simp] theorem gapPermutation_marker (σ : Equiv.Perm A) (g : B ↪ A) (b : B) :
    gapPermutation σ g (.inr b) = .inl (σ (g b)) := by rfl

/-- Inserted markers are never consecutive. -/
theorem gapPermutation_no_marker_adjacency (σ : Equiv.Perm A) (g : B ↪ A) (b c : B) :
    gapPermutation σ g (.inr b) ≠ .inr c := by simp

theorem gapPermutation_ordinary_step (σ : Equiv.Perm A) (g : B ↪ A) (a : A) :
    (gapPermutation σ g).SameCycle (.inl a) (.inl (σ a)) := by
  classical
  by_cases h : ∃ b, g b = a
  · obtain ⟨b, rfl⟩ := h
    have h₁ : (gapPermutation σ g).SameCycle (.inl (g b)) (.inr b) := by
      convert (Equiv.Perm.SameCycle.rfl (f := gapPermutation σ g)
        (x := Sum.inl (g b))).apply_right using 1
      exact (gapNext_gap σ g b).symm
    exact h₁.trans (by simpa using
      (Equiv.Perm.SameCycle.rfl (f := gapPermutation σ g) (x := Sum.inr b)).apply_right)
  · have he : gapPermutation σ g (.inl a) = .inl (σ a) := by
      simp [gapPermutation, gapNext, h]
    rw [← he]
    exact Equiv.Perm.SameCycle.rfl.apply_right

theorem gapPermutation_ordinary_pow (σ : Equiv.Perm A) (g : B ↪ A) (a : A) (n : ℕ) :
    (gapPermutation σ g).SameCycle (.inl a) (.inl ((σ ^ n) a)) := by
  induction n with
  | zero => exact Equiv.Perm.SameCycle.rfl
  | succ n ih =>
    rw [pow_succ', Equiv.Perm.mul_apply]
    exact ih.trans (gapPermutation_ordinary_step σ g _)

/-- Inserting at most one marker in each ordinary gap preserves one cyclic component. -/
theorem gapPermutation_isCycleOn [Finite A] (σ : Equiv.Perm A) (g : B ↪ A)
    (hσ : σ.IsCycleOn Set.univ) : (gapPermutation σ g).IsCycleOn Set.univ := by
  classical
  have ho : ∀ a c : A, (gapPermutation σ g).SameCycle (.inl a) (.inl c) := by
    intro a c
    obtain ⟨n, hn⟩ := hσ.exists_pow_eq' Set.finite_univ (Set.mem_univ a) (Set.mem_univ c)
    simpa only [hn] using gapPermutation_ordinary_pow σ g a n
  have hx : ∀ x : A ⊕ B, ∃ a : A, (gapPermutation σ g).SameCycle x (.inl a) := by
    intro x
    cases x with
    | inl a => exact ⟨a, Equiv.Perm.SameCycle.rfl⟩
    | inr b =>
      exact ⟨σ (g b), by simpa using
        (Equiv.Perm.SameCycle.rfl (f := gapPermutation σ g) (x := Sum.inr b)).apply_right⟩
  refine ⟨⟨Set.mapsTo_univ _ _, (gapPermutation σ g).injective.injOn, (gapPermutation σ g).surjective.surjOn⟩, ?_⟩
  intro x _ y _
  obtain ⟨a, ha⟩ := hx x
  obtain ⟨b, hb⟩ := hx y
  exact ha.trans ((ho a b).trans hb.symm)

end LooseHamilton.BlockEnumeration
