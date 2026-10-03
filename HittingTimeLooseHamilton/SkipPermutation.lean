module

public import HittingTimeLooseHamilton.GapPermutation

public section

namespace LooseHamilton.BlockEnumeration
variable {A B : Type*}

/-- No two deleted labels are consecutive. -/
@[expose] def Separated (σ : Equiv.Perm (A ⊕ B)) : Prop := ∀ b, ∃ a, σ (.inr b) = .inl a

theorem Separated.symm {σ : Equiv.Perm (A ⊕ B)} (h : Separated σ) : Separated σ.symm := by
  intro b
  cases he : σ.symm (.inr b) with
  | inl a => exact ⟨a, rfl⟩
  | inr c =>
    have hh := congrArg σ he
    obtain ⟨a, ha⟩ := h c
    simp only [Equiv.apply_symm_apply, ha] at hh
    cases hh

/-- Successor of a retained label after deleting all marked labels. -/
@[expose] noncomputable def skipNext (σ : Equiv.Perm (A ⊕ B)) (h : Separated σ) (a : A) : A :=
  Sum.elim id (fun b => (h b).choose) (σ (.inl a))

theorem skipNext_direct {σ : Equiv.Perm (A ⊕ B)} (h : Separated σ)
    {a c : A} (he : σ (.inl a) = .inl c) : skipNext σ h a = c := by
  simp [skipNext, he]

theorem skipNext_through {σ : Equiv.Perm (A ⊕ B)} (h : Separated σ)
    {a c : A} {b : B} (he : σ (.inl a) = .inr b) (hf : σ (.inr b) = .inl c) :
    skipNext σ h a = c := by
  simp only [skipNext, he, Sum.elim_inr]
  exact Sum.inl.inj ((h b).choose_spec.symm.trans hf)

theorem skipNext_inverse {σ : Equiv.Perm (A ⊕ B)} (h : Separated σ) (a : A) :
    skipNext σ.symm h.symm (skipNext σ h a) = a := by
  cases he : σ (.inl a) with
  | inl c =>
    rw [skipNext_direct h he]
    exact skipNext_direct h.symm (σ.symm_apply_eq.mpr he.symm)
  | inr b =>
    obtain ⟨c, hc⟩ := h b
    rw [skipNext_through h he hc]
    exact skipNext_through h.symm (σ.symm_apply_eq.mpr hc.symm)
      (σ.symm_apply_eq.mpr he.symm)

/-- Contract a full permutation by skipping isolated deleted labels. -/
@[expose] noncomputable def skipPermutation (σ : Equiv.Perm (A ⊕ B)) (h : Separated σ) : Equiv.Perm A where
  toFun := skipNext σ h
  invFun := skipNext σ.symm h.symm
  left_inv := skipNext_inverse h
  right_inv := by intro a; exact skipNext_inverse h.symm a

@[simp] theorem skipPermutation_apply (σ : Equiv.Perm (A ⊕ B)) (h : Separated σ) (a : A) :
    skipPermutation σ h a = skipNext σ h a := rfl

/-- Project deleted labels to their next retained label. -/
@[expose] noncomputable def skipProjection (σ : Equiv.Perm (A ⊕ B)) (h : Separated σ) : A ⊕ B → A :=
  Sum.elim id (fun b => (h b).choose)

@[simp] theorem skipProjection_inl (σ : Equiv.Perm (A ⊕ B)) (h : Separated σ) (a : A) :
    skipProjection σ h (.inl a) = a := rfl

theorem skipProjection_step (σ : Equiv.Perm (A ⊕ B)) (h : Separated σ) (x : A ⊕ B) :
    (skipPermutation σ h).SameCycle (skipProjection σ h x) (skipProjection σ h (σ x)) := by
  cases x with
  | inl a =>
    change (skipPermutation σ h).SameCycle a (skipPermutation σ h a)
    exact Equiv.Perm.SameCycle.rfl.apply_right
  | inr b =>
    rw [(h b).choose_spec]
    exact Equiv.Perm.SameCycle.rfl

theorem skipProjection_pow (σ : Equiv.Perm (A ⊕ B)) (h : Separated σ) (x : A ⊕ B) (n : ℕ) :
    (skipPermutation σ h).SameCycle (skipProjection σ h x) (skipProjection σ h ((σ ^ n) x)) := by
  induction n with
  | zero => exact Equiv.Perm.SameCycle.rfl
  | succ n ih =>
    rw [pow_succ', Equiv.Perm.mul_apply]
    exact ih.trans (skipProjection_step σ h _)

/-- Deleting nonconsecutive labels from a single cyclic component leaves one component. -/
theorem skipPermutation_isCycleOn [Finite A] [Finite B] (σ : Equiv.Perm (A ⊕ B))
    (h : Separated σ) (hσ : σ.IsCycleOn Set.univ) :
    (skipPermutation σ h).IsCycleOn Set.univ := by
  refine ⟨⟨Set.mapsTo_univ _ _, (skipPermutation σ h).injective.injOn,
    (skipPermutation σ h).surjective.surjOn⟩, ?_⟩
  intro a _ c _
  obtain ⟨n, hn⟩ := hσ.exists_pow_eq' Set.finite_univ (Set.mem_univ (.inl a))
    (Set.mem_univ (.inl c))
  simpa only [hn, skipProjection_inl] using skipProjection_pow σ h (.inl a) n

end LooseHamilton.BlockEnumeration
