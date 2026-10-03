module

public import HittingTimeLooseHamilton.RootedPermutation
public import HittingTimeLooseHamilton.SkipPermutation

public section

namespace LooseHamilton.BlockEnumeration
variable {A B : Type*}

/-- The gap of a deleted marker is its preceding ordinary label. -/
@[expose] noncomputable def gapEmbedding (σ : Equiv.Perm (A ⊕ B)) (h : Separated σ) : B ↪ A where
  toFun b := (h.symm b).choose
  inj' := by
    intro b c he
    change (h.symm b).choose = (h.symm c).choose at he
    have hb := (h.symm b).choose_spec
    have hc := (h.symm c).choose_spec
    rw [he] at hb
    exact Sum.inr.inj (σ.symm.injective (hb.trans hc.symm))

theorem gapEmbedding_predecessor (σ : Equiv.Perm (A ⊕ B)) (h : Separated σ) (b : B) :
    σ.symm (.inr b) = .inl (gapEmbedding σ h b) := (h.symm b).choose_spec

theorem gapEmbedding_successor (σ : Equiv.Perm (A ⊕ B)) (h : Separated σ) (b : B) :
    σ (.inl (gapEmbedding σ h b)) = .inr b :=
  σ.apply_eq_iff_eq_symm_apply.mpr (gapEmbedding_predecessor σ h b).symm

theorem gapPermutation_separated (σ : Equiv.Perm A) (g : B ↪ A) :
    Separated (gapPermutation σ g) := fun b => ⟨σ (g b), rfl⟩

/-- Expansion recovers the original permutation after contraction. -/
theorem gap_skip_inverse (σ : Equiv.Perm (A ⊕ B)) (h : Separated σ) :
    gapPermutation (skipPermutation σ h) (gapEmbedding σ h) = σ := by
  apply Equiv.ext
  intro x
  cases x with
  | inl a =>
    cases he : σ (.inl a) with
    | inl c =>
      have hn : ¬ ∃ b, gapEmbedding σ h b = a := by
        rintro ⟨b, hb⟩
        have hh := gapEmbedding_successor σ h b
        rw [hb, he] at hh
        cases hh
      simp only [gapPermutation, Equiv.coe_fn_mk, gapNext, Sum.elim_inl, dif_neg hn]
      rw [skipPermutation_apply, skipNext_direct h he]
    | inr b =>
      have hb : gapEmbedding σ h b = a := by
        apply Sum.inl.inj
        rw [← gapEmbedding_predecessor, σ.symm_apply_eq.mpr he.symm]
      rw [← hb]
      exact gapNext_gap _ _ _
  | inr b =>
    obtain ⟨c, hc⟩ := h b
    rw [gapPermutation_marker, hc, skipPermutation_apply,
      skipNext_through h (gapEmbedding_successor σ h b) hc]

/-- Contraction recovers the ordinary cycle after insertion. -/
theorem skip_gap_inverse (σ : Equiv.Perm A) (g : B ↪ A) :
    skipPermutation (gapPermutation σ g) (gapPermutation_separated σ g) = σ := by
  classical
  apply Equiv.ext
  intro a
  change skipNext _ _ a = σ a
  by_cases h : ∃ b, g b = a
  · obtain ⟨b, rfl⟩ := h
    exact skipNext_through _ (gapNext_gap σ g b) rfl
  · exact skipNext_direct _ (by simp [gapPermutation, gapNext, h])

/-- The gaps are recovered exactly by taking predecessors of the inserted markers. -/
theorem gapEmbedding_gap (σ : Equiv.Perm A) (g : B ↪ A) :
    gapEmbedding (gapPermutation σ g) (gapPermutation_separated σ g) = g := by
  apply Function.Embedding.ext
  intro b
  apply Sum.inl.inj
  apply (gapPermutation σ g).injective
  rw [gapEmbedding_successor]
  exact (gapNext_gap σ g b).symm

/-- Actual full cyclic permutations with no consecutive marked labels. -/
@[expose] def SeparatedFullCycle (A B : Type*) :=
  {σ : FullCycle (A ⊕ B) // Separated σ.val}

@[expose] noncomputable instance [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B] :
    Fintype (SeparatedFullCycle A B) := by
  classical
  unfold SeparatedFullCycle
  infer_instance

/-- Gap insertion is a bijection with the actual separated cyclic permutations. -/
@[expose] noncomputable def separatedFullCycleEquiv [Finite A] [Finite B] :
    (FullCycle A × (B ↪ A)) ≃ SeparatedFullCycle A B where
  toFun p := ⟨⟨gapPermutation p.1.val p.2,
    gapPermutation_isCycleOn p.1.val p.2 p.1.property⟩,
      gapPermutation_separated p.1.val p.2⟩
  invFun σ := ⟨⟨skipPermutation σ.val.val σ.property,
    skipPermutation_isCycleOn σ.val.val σ.property σ.val.property⟩,
      gapEmbedding σ.val.val σ.property⟩
  left_inv p := by
    apply Prod.ext
    · apply Subtype.ext
      exact skip_gap_inverse _ _
    · exact gapEmbedding_gap _ _
  right_inv σ := by
    apply Subtype.ext
    apply Subtype.ext
    exact gap_skip_inverse _ _

/-- Realize separated block-order codes on the actual ordinary and marked labels. -/
@[expose] noncomputable def separatedOrderLabelEquiv [Fintype A] [Fintype B] {k s : ℕ}
    (hs : s < k) (hA : Fintype.card A = k - s) (hB : Fintype.card B = s) :
    SeparatedOrder k s ≃ SeparatedFullCycle A B :=
  (Equiv.prodCongr (rootedOrderLabelEquiv (Nat.sub_pos_of_lt hs) hA)
    (Equiv.embeddingCongr (Fintype.equivFinOfCardEq hB).symm
      (Fintype.equivFinOfCardEq hA).symm)).trans separatedFullCycleEquiv

/-- The finite code count is the count of genuine separated cyclic orders. -/
theorem card_separatedFullCycle_fin (m s : ℕ) :
    Fintype.card (SeparatedFullCycle (Fin (m + 1)) (Fin s)) =
      m.factorial * (m + 1).descFactorial s := by
  rw [← Fintype.card_congr (separatedFullCycleEquiv (A := Fin (m+1)) (B := Fin s))]
  simp

end LooseHamilton.BlockEnumeration
