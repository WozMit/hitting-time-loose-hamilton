module

public import HittingTimeLooseHamilton.WitnessEncoding
public import HittingTimeLooseHamilton.SeparatedCycles

public section

noncomputable section
namespace LooseHamilton
open BlockEnumeration
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- On marker/ordinary block labels, every marked block is followed by an ordinary one. -/
@[expose] def BlockSeparated {M J : Type*} (σ : Equiv.Perm (M ⊕ J)) : Prop :=
  ∀ m, ∃ j, σ (.inl m) = .inr j

/-- Exchange the ordinary-first convention for the marker-first convention. -/
@[expose] def separatedFullCycleSwap {A B : Type*} :
    SeparatedFullCycle A B ≃ {σ : FullCycle (B ⊕ A) // BlockSeparated σ.val} :=
  (fullCycleRelabel (Equiv.sumComm A B)).subtypeEquiv (by
    intro σ
    change Separated σ.val ↔ BlockSeparated ((Equiv.sumComm A B).permCongr σ.val)
    constructor
    · intro h b
      obtain ⟨a, ha⟩ := h b
      exact ⟨a, by simp only [Equiv.permCongr_apply, Equiv.sumComm_apply,
        Equiv.sumComm_symm, Sum.swap_inl, ha, Sum.swap_inl]⟩
    · intro h b
      obtain ⟨a, ha⟩ := h b
      refine ⟨a, ?_⟩
      have hh := congrArg Sum.swap ha
      simpa only [Equiv.permCongr_apply, Equiv.sumComm_apply,
        Equiv.sumComm_symm, Sum.swap_inl, Sum.swap_swap, Sum.swap_inr] using hh)

/-- The actual block permutation represented by the rooted order in a code. -/
@[expose] def codeOrderEquiv (k : ℕ) (hk : 0 < k) (markers : Finset (Finset V))
    (hsk : markers.card ≤ k) (J : ↥(ordinaryJunctionChoices markers k)) :
    RootedOrder k ≃ FullCycle (↥markers ⊕ ↥J.val) :=
  (rootedOrderCycleEquiv k hk).trans
    (fullCycleRelabel (codeBlockLabels markers k hsk J).symm)

/-- Separated-order codes are exactly those unrestricted order codes having no adjacent markers. -/
@[expose] def restrictedOrderCodeEquiv (k : ℕ) (markers : Finset (Finset V))
    (hsk : markers.card < k) (J : ↥(ordinaryJunctionChoices markers k)) :
    SeparatedOrder k markers.card ≃
      {o : RootedOrder k // BlockSeparated (codeOrderEquiv k (by omega) markers hsk.le J o).val} :=
  ((separatedOrderLabelEquiv hsk
      (show Fintype.card ↥J.val = k - markers.card by
        simpa only [Fintype.card_coe] using
          ((mem_ordinaryJunctionChoices _ _ _).mp J.property).2)
      (Fintype.card_coe markers)).trans separatedFullCycleSwap).trans
    ((codeOrderEquiv k (by omega) markers hsk.le J).subtypeEquivOfSubtype
      (p := fun σ => BlockSeparated σ.val)).symm

/-- The separated-block predicate on the existing complete-host data type. -/
@[expose] def codeSeparated {r k : ℕ} {markers : Finset (Finset V)} {root : Finset V}
    (hk : 0 < k) (hsk : markers.card ≤ k) (c : CompleteHostCode r k markers root) : Prop :=
  BlockSeparated (codeOrderEquiv k hk markers hsk c.1 c.2.2.1).val

/-- Restricting the actual block successor to separated markers is exactly the allowed code type. -/
@[expose] def allowedHostCodeEquiv {r k : ℕ} {markers : Finset (Finset V)} {root : Finset V}
    (hsk : markers.card < k) :
    AllowedHostCode r k markers root ≃
      {c : CompleteHostCode r k markers root // codeSeparated (by omega) hsk.le c} where
  toFun c :=
    let o := restrictedOrderCodeEquiv k markers hsk c.1 c.2.2.1
    ⟨⟨c.1, c.2.1, o.val, c.2.2.2⟩, o.property⟩
  invFun c :=
    ⟨c.val.1, c.val.2.1,
      (restrictedOrderCodeEquiv k markers hsk c.val.1).symm ⟨c.val.2.2.1, c.property⟩,
      c.val.2.2.2⟩
  left_inv c := by
    rcases c with ⟨J, d, o, P⟩
    change (⟨J, d, (restrictedOrderCodeEquiv k markers hsk J).symm
      (restrictedOrderCodeEquiv k markers hsk J o), P⟩ : AllowedHostCode r k markers root) = _
    rw [Equiv.symm_apply_apply]
  right_inv c := by
    apply Subtype.ext
    rcases c with ⟨⟨J, d, o, P⟩, hc⟩
    dsimp only
    have h := (restrictedOrderCodeEquiv k markers hsk J).apply_symm_apply ⟨o, hc⟩
    have he := congrArg Subtype.val h
    change (⟨J, d, _, P⟩ : CompleteHostCode r k markers root) = _
    rw [he]

end LooseHamilton
