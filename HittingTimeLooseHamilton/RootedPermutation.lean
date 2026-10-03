module

public import HittingTimeLooseHamilton.CyclicTraversal

public section

namespace LooseHamilton.BlockEnumeration

/-- Full directed cyclic permutations on a finite labelled set. -/
@[expose] def FullCycle (A : Type*) := {σ : Equiv.Perm A // σ.IsCycleOn Set.univ}

@[expose] noncomputable instance {A : Type*} [Fintype A] [DecidableEq A] : Fintype (FullCycle A) :=
  by
    classical
    unfold FullCycle
    infer_instance

/-- Relabelling preserves composition of permutations. -/
@[expose] def permutationRelabel {A B : Type*} (e : A ≃ B) : Equiv.Perm A ≃* Equiv.Perm B where
  toEquiv := Equiv.permCongr e
  map_mul' σ τ := by ext x; simp [Equiv.Perm.mul_apply]

theorem cycle_relabel {A B : Type*} (e : A ≃ B) (σ : Equiv.Perm A)
    (hσ : σ.IsCycleOn Set.univ) : (e.permCongr σ).IsCycleOn Set.univ := by
  refine ⟨⟨Set.mapsTo_univ _ _, (e.permCongr σ).injective.injOn,
    (e.permCongr σ).surjective.surjOn⟩, ?_⟩
  intro x _ y _
  obtain ⟨n, hn⟩ := hσ.2 (Set.mem_univ (e.symm x)) (Set.mem_univ (e.symm y))
  refine ⟨n, ?_⟩
  change ((permutationRelabel e σ) ^ n) x = y
  rw [← map_zpow]
  change e ((σ ^ n) (e.symm x)) = y
  rw [hn, e.apply_symm_apply]

/-- Relabel actual full cyclic permutations along an arbitrary equivalence. -/
@[expose] def fullCycleRelabel {A B : Type*} (e : A ≃ B) : FullCycle A ≃ FullCycle B where
  toFun σ := ⟨e.permCongr σ.val, cycle_relabel e σ.val σ.property⟩
  invFun τ := ⟨e.symm.permCongr τ.val, cycle_relabel e.symm τ.val τ.property⟩
  left_inv σ := by apply Subtype.ext; ext a; simp
  right_inv τ := by apply Subtype.ext; ext a; simp

/-- A cyclic traversal whose initial label is zero. -/
abbrev RootedTraversal (n : ℕ) := {e : Equiv.Perm (Fin (n + 1)) // e 0 = 0}

@[expose] noncomputable def rootedTraversalEquiv (n : ℕ) : Equiv.Perm (Fin n) ≃ RootedTraversal n where
  toFun p := ⟨Equiv.Perm.decomposeFin.symm (0, p), by simp⟩
  invFun e := (Equiv.Perm.decomposeFin e.val).2
  left_inv p := by simp
  right_inv e := by
    apply Subtype.ext
    apply Equiv.Perm.decomposeFin.injective
    simp only [Equiv.apply_symm_apply]
    apply Prod.ext
    · have h := Equiv.Perm.decomposeFin_symm_apply_zero
        (Equiv.Perm.decomposeFin e.val).1 (Equiv.Perm.decomposeFin e.val).2
      simpa only [Prod.mk.eta, Equiv.symm_apply_apply, e.property] using h
    · rfl

theorem finRotate_isCycleOn (n : ℕ) : (finRotate (n + 1)).IsCycleOn Set.univ := by
  cases n with
  | zero => exact @Equiv.Perm.isCycleOn_of_subsingleton (Fin 1) _ _ _
  | succ n =>
    have h := isCycle_finRotate (n := n)
    convert h.isCycleOn using 1
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
    have hx : x ∈ (finRotate (n + 2)).support := by rw [support_finRotate]; simp
    exact iff_of_true trivial (Equiv.Perm.mem_support.mp hx)

/-- Successor of a cyclic listing of all labels. -/
@[expose] def traversalSuccessor {n : ℕ} (e : Equiv.Perm (Fin (n + 1))) : Equiv.Perm (Fin (n + 1)) :=
  e * finRotate (n + 1) * e⁻¹

theorem traversalSuccessor_cycle {n : ℕ} (e : Equiv.Perm (Fin (n + 1))) :
    (traversalSuccessor e).IsCycleOn Set.univ := by
  simpa [traversalSuccessor, Set.image_univ_of_surjective e.surjective] using (finRotate_isCycleOn n).conj (g := e)

@[simp] theorem traversalSuccessor_step {n : ℕ} (e : Equiv.Perm (Fin (n + 1)))
    (i : Fin (n + 1)) : traversalSuccessor e (e i) = e (finRotate _ i) := by
  simp [traversalSuccessor, Equiv.Perm.mul_apply]

/-- Rooted traversal of a full cyclic permutation. -/
@[expose] noncomputable def fullCycleTraversal {n : ℕ} (σ : FullCycle (Fin (n + 1))) :
    Equiv.Perm (Fin (n + 1)) :=
  (finCongr (Fintype.card_fin (n + 1))).symm.trans (cycleTraversal σ.val σ.property 0)

@[simp] theorem fullCycleTraversal_apply {n : ℕ} (σ : FullCycle (Fin (n + 1)))
    (i : Fin (n + 1)) : fullCycleTraversal σ i = (σ.val ^ i.val) 0 := rfl

@[simp] theorem fullCycleTraversal_zero {n : ℕ} (σ : FullCycle (Fin (n + 1))) :
    fullCycleTraversal σ 0 = 0 := rfl

theorem finCongr_rotate {m n : ℕ} (h : m = n) (i : Fin m) :
    finCongr h (finRotate m i) = finRotate n (finCongr h i) := by
  subst n
  rfl

@[simp] theorem fullCycleTraversal_step {n : ℕ} (σ : FullCycle (Fin (n + 1)))
    (i : Fin (n + 1)) : fullCycleTraversal σ (finRotate _ i) = σ.val (fullCycleTraversal σ i) := by
  unfold fullCycleTraversal
  simp only [Equiv.trans_apply, finCongr_symm, finCongr_rotate]
  exact cycleTraversal_rotate σ.val σ.property 0 _

/-- A root and the successor map determine the cyclic traversal uniquely. -/
theorem rootedTraversal_unique {n : ℕ} (e f : Equiv.Perm (Fin (n + 1)))
    (hz : e 0 = f 0) (hstep : ∀ i, e (finRotate _ i) =
      traversalSuccessor f (e i)) : e = f := by
  apply Equiv.ext
  intro i
  obtain ⟨i, hi⟩ := i
  induction i with
  | zero => exact hz
  | succ i ih =>
    have hil : i < n := by omega
    have h := hstep ⟨i, by omega⟩
    rw [finRotate_of_lt hil, ih (by omega), traversalSuccessor_step,
      finRotate_of_lt hil] at h
    exact h

@[expose] noncomputable def rootedFullCycleEquiv (n : ℕ) : RootedTraversal n ≃ FullCycle (Fin (n + 1)) where
  toFun e := ⟨traversalSuccessor e.val, traversalSuccessor_cycle e.val⟩
  invFun σ := ⟨fullCycleTraversal σ, fullCycleTraversal_zero σ⟩
  left_inv e := by
    apply Subtype.ext
    apply rootedTraversal_unique
    · exact (fullCycleTraversal_zero _).trans e.property.symm
    · intro i
      exact fullCycleTraversal_step _ i
  right_inv σ := by
    apply Subtype.ext
    ext a
    obtain ⟨i, rfl⟩ := (fullCycleTraversal σ).surjective a
    rw [traversalSuccessor_step, fullCycleTraversal_step]

/-- Rooting removes the rotation ambiguity: full cyclic permutations of `n+1` labels
are in bijection with permutations of the `n` remaining labels. -/
@[expose] noncomputable def rootedOrderFullCycleEquiv (n : ℕ) :
    Equiv.Perm (Fin n) ≃ FullCycle (Fin (n + 1)) :=
  (rootedTraversalEquiv n).trans (rootedFullCycleEquiv n)

/-- Realize the rooted-order code on an arbitrary set of `k` block labels. -/
@[expose] noncomputable def rootedOrderLabelEquiv {A : Type*} [Fintype A] {k : ℕ}
    (hk : 0 < k) (hcard : Fintype.card A = k) : RootedOrder k ≃ FullCycle A :=
  (rootedOrderFullCycleEquiv (k - 1)).trans
    (fullCycleRelabel ((finCongr (Nat.sub_add_cancel hk)).trans
      (Fintype.equivFinOfCardEq hcard).symm))

@[simp] theorem card_fullCycle_fin_succ (n : ℕ) :
    Fintype.card (FullCycle (Fin (n + 1))) = n.factorial := by
  rw [← Fintype.card_congr (rootedOrderFullCycleEquiv n)]
  simp [Fintype.card_perm]

end LooseHamilton.BlockEnumeration
