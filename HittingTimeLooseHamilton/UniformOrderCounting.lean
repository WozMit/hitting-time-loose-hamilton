module

public import HittingTimeLooseHamilton.KahnOrdering
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fintype.Perm

public section

/-! Exact boundary fibres in a uniformly sampled finite order. -/
noncomputable section
namespace LooseHamilton
open Finset
variable {A : Type*} [Fintype A] [DecidableEq A]

abbrev FiniteOrder (A : Type*) [Fintype A] := A ≃ Fin (Fintype.card A)

@[expose] def orderPrefix (σ : FiniteOrder A) (m : ℕ) : Finset A :=
  univ.filter (fun a => (σ a).val < m)

@[simp] theorem mem_orderPrefix (σ : FiniteOrder A) (m : ℕ) (a : A) :
    a ∈ orderPrefix σ m ↔ (σ a).val < m := by simp [orderPrefix]

theorem orderPrefix_card (σ : FiniteOrder A) (m : ℕ) (hm : m ≤ Fintype.card A) :
    (orderPrefix σ m).card = m := by
  have he : orderPrefix σ m = (univ : Finset (Fin m)).image
      (fun i => σ.symm ⟨i.val, lt_of_lt_of_le i.isLt hm⟩) := by
    ext a
    simp only [mem_orderPrefix, mem_image, mem_univ, true_and]
    constructor
    · intro ha
      exact ⟨⟨(σ a).val,ha⟩, σ.symm_apply_apply a⟩
    · rintro ⟨i, rfl⟩
      simp
  rw [he, card_image_of_injective]
  · simp
  · intro i j hij
    exact Fin.ext (congrArg (fun x : Fin (Fintype.card A) => x.val) (σ.symm.injective hij))

abbrev PointedSubset (A : Type*) [Fintype A] [DecidableEq A] (m : ℕ) :=
  Σ S : ↥((univ : Finset A).powersetCard m), ↥S.val

@[expose] def orderBoundary (σ : FiniteOrder A) (m : ℕ) (hm : m ≤ Fintype.card A) (hpos : 0 < m) :
    A := σ.symm ⟨m-1, by omega⟩

@[expose] def orderPointedPrefix (m : ℕ) (hm : m ≤ Fintype.card A) (hpos : 0 < m)
    (σ : FiniteOrder A) : PointedSubset A m :=
  ⟨⟨orderPrefix σ m, mem_powersetCard.mpr ⟨subset_univ _,orderPrefix_card σ m hm⟩⟩,
    ⟨orderBoundary σ m hm hpos, by simp [orderBoundary]; omega⟩⟩

theorem card_pointedSubset (m : ℕ) :
    Fintype.card (PointedSubset A m) = m * (Fintype.card A).choose m := by
  rw [Fintype.card_sigma]
  have hh : ∀ S : ↥((univ : Finset A).powersetCard m), Fintype.card ↥S.val = m := by
    intro S
    simpa only [Fintype.card_coe] using (mem_powersetCard.mp S.property).2
  simp_rw [hh]
  simp [card_powersetCard, mul_comm]

private theorem pointed_subset_transport (S T : Finset A) (hc : S.card = T.card)
    (a : ↥S) (b : ↥T) :
    ∃ g : Equiv.Perm A, g a.val = b.val ∧ ∀ x, x ∈ S ↔ g x ∈ T := by
  let e : ↥S ≃ ↥T := Finset.equivOfCardEq hc
  let g₀ : Equiv.Perm A := e.extendSubtype
  have hmem : ∀ x, x ∈ S ↔ g₀ x ∈ T := by
    intro x
    constructor
    · exact e.extendSubtype_mem x
    · intro hx
      by_contra hn
      exact e.extendSubtype_not_mem x hn hx
  have hga : g₀ a.val ∈ T := (hmem _).mp a.property
  have hswap : ∀ x, Equiv.swap (g₀ a.val) b.val x ∈ T ↔ x ∈ T := by
    intro x
    by_cases hx : x = g₀ a.val
    · subst x; simp [hga,b.property]
    by_cases hb : x = b.val
    · subst x; simp [hga,b.property]
    rw [Equiv.swap_apply_of_ne_of_ne hx hb]
  refine ⟨g₀.trans (Equiv.swap (g₀ a.val) b.val),by simp,?_⟩
  intro x
  simpa only [Equiv.trans_apply,hswap] using hmem x

/-- The fibre is described directly by its prefix set and its last element. -/
theorem orderPointedPrefix_eq_iff (m : ℕ) (hm : m ≤ Fintype.card A) (hpos : 0 < m)
    (σ : FiniteOrder A) (b : PointedSubset A m) :
    orderPointedPrefix m hm hpos σ = b ↔
      orderPrefix σ m = b.1.val ∧ (σ b.2.val).val = m-1 := by
  constructor
  · intro h
    subst b
    exact ⟨rfl,by simp [orderPointedPrefix,orderBoundary]⟩
  · rintro ⟨hs,he⟩
    rcases b with ⟨⟨S,hS⟩,⟨a,ha⟩⟩
    simp only at hs he
    have ha' : orderBoundary σ m hm hpos = a := by
      apply σ.injective
      simpa only [orderBoundary,Equiv.apply_symm_apply] using (Fin.ext he).symm
    cases hs
    simp only [orderPointedPrefix]
    congr 1
    exact Subtype.ext ha'

/-- Relabelling acts transitively on the pointed prefix fibres. -/
theorem orderPointedPrefix_fibres_equal (m : ℕ) (hm : m ≤ Fintype.card A) (hpos : 0 < m)
    (b c : PointedSubset A m) :
    (univ.filter (fun σ : FiniteOrder A => orderPointedPrefix m hm hpos σ = b)).card =
      (univ.filter (fun σ : FiniteOrder A => orderPointedPrefix m hm hpos σ = c)).card := by
  classical
  have hc : b.1.val.card = c.1.val.card :=
    (mem_powersetCard.mp b.1.property).2.trans (mem_powersetCard.mp c.1.property).2.symm
  obtain ⟨g,hg,hmem⟩ := pointed_subset_transport b.1.val c.1.val hc b.2 c.2
  let e : FiniteOrder A ≃ FiniteOrder A := Equiv.equivCongr g (Equiv.refl _)
  apply Kahn.Ordering.card_event_eq_of_equiv _ _ e
  intro σ
  rw [orderPointedPrefix_eq_iff,orderPointedPrefix_eq_iff]
  have hp : orderPrefix σ m = b.1.val ↔ orderPrefix (e σ) m = c.1.val := by
    constructor
    · intro hs
      ext x
      rw [mem_orderPrefix]
      change ((σ (g.symm x)).val < m) ↔ x ∈ c.1.val
      rw [← mem_orderPrefix,hs,hmem]
      simp
    · intro hs
      ext x
      rw [mem_orderPrefix,hmem]
      have hh := congrArg (fun T => g x ∈ T) hs
      simpa [mem_orderPrefix,e,Equiv.equivCongr] using Iff.of_eq hh
  have hg' : g.symm c.2.val = b.2.val := g.symm_apply_eq.mpr hg.symm
  have hrank : ((e σ) c.2.val).val = (σ b.2.val).val := by
    change (σ (g.symm c.2.val)).val = _
    rw [hg']
  rw [hrank]
  exact and_congr hp Iff.rfl

/-- Under the actual uniform finite-order law, a fixed pointed prefix has
probability `1 / (m * choose N m)`. -/
theorem uniform_order_boundary_probability (m : ℕ) (hm : m ≤ Fintype.card A) (hpos : 0 < m)
    (S : Finset A) (hS : S.card = m) (a : A) (ha : a ∈ S) :
    ((univ.filter (fun σ : FiniteOrder A =>
      orderPrefix σ m = S ∧ (σ a).val = m-1)).card : ℝ) /
        Fintype.card (FiniteOrder A) =
      1 / ((m : ℝ) * (Fintype.card A).choose m) := by
  classical
  letI : Nonempty (FiniteOrder A) := ⟨Fintype.equivFin A⟩
  let b : PointedSubset A m := ⟨⟨S,mem_powersetCard.mpr ⟨subset_univ _,hS⟩⟩,⟨a,ha⟩⟩
  have h := Kahn.Ordering.uniform_fibre_probability (orderPointedPrefix m hm hpos) b
    (fun c => orderPointedPrefix_fibres_equal m hm hpos c b)
  simp only [orderPointedPrefix_eq_iff, b, card_pointedSubset, Nat.cast_mul] at h
  exact h

end LooseHamilton
