module

public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Real.Basic
public import Mathlib.Logic.Equiv.Fintype
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

public section

/-!
# Finite subset counting for Kahn's random-ordering argument

This file proves the counting part of the survivor-set calculation in
Kahn, *Asymptotics for Shamir's Problem*, equations (36)--(38).
It does not assert that the survivor set of a uniform vertex ordering is uniform;
that separate symmetry statement is needed before applying these counts.
-/

namespace Kahn.Ordering

open Finset

variable {α : Type*} [DecidableEq α]

/-- A bijective symmetry transporting one event to another preserves its
cardinality. This is the finite uniform-probability symmetry principle. -/
theorem card_event_eq_of_equiv {Ω : Type*} [Fintype Ω]
    (P Q : Ω → Prop) [DecidablePred P] [DecidablePred Q]
    (e : Ω ≃ Ω) (he : ∀ ω, P ω ↔ Q (e ω)) :
    (univ.filter P).card = (univ.filter Q).card := by
  apply card_equiv e
  intro ω
  simpa only [mem_filter, mem_univ, true_and] using he ω

/-- If the fibres of a finite-valued observable are equicardinal, each fibre
has reciprocal-cardinality probability under the uniform law. -/
theorem uniform_fibre_probability {Ω B : Type*} [Fintype Ω] [Nonempty Ω]
    [Fintype B] [DecidableEq B] (f : Ω → B) (b : B)
    (hequal : ∀ c, (univ.filter (fun ω => f ω = c)).card =
      (univ.filter (fun ω => f ω = b)).card) :
    ((univ.filter (fun ω => f ω = b)).card : ℝ) / Fintype.card Ω =
      1 / Fintype.card B := by
  have hcard : Fintype.card Ω =
      Fintype.card B * (univ.filter (fun ω => f ω = b)).card := by
    calc
      Fintype.card Ω = ∑ c : B, (univ.filter (fun ω => f ω = c)).card :=
        card_eq_sum_card_fiberwise (fun _ _ => mem_univ _)
      _ = Fintype.card B * (univ.filter (fun ω => f ω = b)).card := by
        simp_rw [hequal]
        simp
  have hΩ : (Fintype.card Ω : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  haveI : Nonempty B := ⟨b⟩
  have hB : (Fintype.card B : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hcardR : (Fintype.card Ω : ℝ) =
      (Fintype.card B : ℝ) * (univ.filter (fun ω => f ω = b)).card := by
    simpa only [Nat.cast_mul] using congrArg (fun n : ℕ => (n : ℝ)) hcard
  apply (div_eq_div_iff hΩ hB).mpr
  rw [one_mul, hcardR, mul_comm]

/-- The stabilizer of `v` in the permutation group acts transitively on
subsets of a fixed size avoiding `v`. -/
theorem exists_perm_fix_maps_subsets [Fintype α] (S T : Finset α)
    (hcard : S.card = T.card) (v : α) (hvS : v ∉ S) (hvT : v ∉ T) :
    ∃ g : Equiv.Perm α, g v = v ∧ ∀ x, x ∈ S ↔ g x ∈ T := by
  classical
  let e : S ≃ T := Finset.equivOfCardEq hcard
  let g₀ : Equiv.Perm α := e.extendSubtype
  have hmem : ∀ x, x ∈ S ↔ g₀ x ∈ T := by
    intro x
    constructor
    · exact e.extendSubtype_mem x
    · intro hx
      by_contra hn
      exact e.extendSubtype_not_mem x hn hx
  have hgv : g₀ v ∉ T := fun hh => hvS ((hmem v).mpr hh)
  have hswap : ∀ x, Equiv.swap (g₀ v) v x ∈ T ↔ x ∈ T := by
    intro x
    by_cases hx : x = g₀ v
    · subst x
      simp [hgv, hvT]
    by_cases hxv : x = v
    · subst x
      simp [hgv, hvT]
    rw [Equiv.swap_apply_of_ne_of_ne hx hxv]
  refine ⟨g₀.trans (Equiv.swap (g₀ v) v), by simp, ?_⟩
  intro x
  simpa only [Equiv.trans_apply, hswap] using hmem x

/-- There are `choose (|S|-|A|) (k-|A|)` size-`k` subsets of `S` containing
the fixed subset `A`, provided `|A| ≤ k`. -/
theorem card_subsets_containing (S A : Finset α) (hAS : A ⊆ S)
    (k : ℕ) (hAk : A.card ≤ k) :
    ((S.powersetCard k).filter (fun U => A ⊆ U)).card =
      Nat.choose (S.card - A.card) (k - A.card) := by
  rw [← card_sdiff_of_subset hAS, ← card_powersetCard]
  apply card_bij (fun U _ => U \ A)
  · intro U hU
    obtain ⟨hU, hAU⟩ := mem_filter.mp hU
    obtain ⟨hUS, hUk⟩ := mem_powersetCard.mp hU
    apply mem_powersetCard.mpr
    exact ⟨sdiff_subset_sdiff hUS (Subset.refl A), by rw [card_sdiff_of_subset hAU, hUk]⟩
  · intro U hU W hW h
    have hAU := (mem_filter.mp hU).2
    have hAW := (mem_filter.mp hW).2
    simpa only [sdiff_union_of_subset hAU, sdiff_union_of_subset hAW] using
      congrArg (fun T : Finset α => T ∪ A) h
  · intro U hU
    obtain ⟨hUSA, hUk⟩ := mem_powersetCard.mp hU
    have hUS : U ⊆ S := (subset_sdiff.mp hUSA).1
    have hUA : Disjoint U A := (subset_sdiff.mp hUSA).2
    refine ⟨U ∪ A, mem_filter.mpr ⟨mem_powersetCard.mpr ⟨union_subset hUS hAS, ?_⟩,
      subset_union_right⟩, union_sdiff_cancel_right hUA⟩
    rw [card_union_of_disjoint hUA, hUk, Nat.sub_add_cancel hAk]

/-- Exact survivor probability, expressed as a ratio of binomial coefficients.
The sample space is explicitly the finite set of all size-`k` subsets of `S`.
The assumptions ensure that this sample space is nonempty. -/
theorem uniform_subset_contains (S A : Finset α) (hAS : A ⊆ S)
    (k : ℕ) (hAk : A.card ≤ k) (_hkS : k ≤ S.card) :
    (((S.powersetCard k).filter (fun U => A ⊆ U)).card : ℝ) /
        (S.powersetCard k).card =
      (Nat.choose (S.card - A.card) (k - A.card) : ℝ) /
        Nat.choose S.card k := by
  rw [card_subsets_containing S A hAS k hAk, card_powersetCard]

/-- The binomial-coefficient ratio in the preceding count is the ratio of
falling factorials used in the paper. -/
theorem choose_ratio_eq_descFactorial_ratio (n k a : ℕ)
    (hkn : k ≤ n) (hak : a ≤ k) :
    ((n - a).choose (k - a) : ℝ) / n.choose k =
      (k.descFactorial a : ℝ) / n.descFactorial a := by
  have hnk : (n.choose k : ℝ) ≠ 0 := by
    exact Nat.cast_ne_zero.mpr (Nat.ne_of_gt (Nat.choose_pos hkn))
  have hna : (n.choose a : ℝ) ≠ 0 := by
    exact Nat.cast_ne_zero.mpr (Nat.ne_of_gt (Nat.choose_pos (hak.trans hkn)))
  have hfac : (a.factorial : ℝ) ≠ 0 := by
    exact Nat.cast_ne_zero.mpr a.factorial_ne_zero
  have hmul : (n.choose k : ℝ) * k.choose a =
      (n.choose a : ℝ) * (n - a).choose (k - a) := by
    simpa only [Nat.cast_mul] using
      congrArg (fun n : ℕ => (n : ℝ)) (Nat.choose_mul hak)
  rw [Nat.descFactorial_eq_factorial_mul_choose,
    Nat.descFactorial_eq_factorial_mul_choose]
  rw [Nat.cast_mul, Nat.cast_mul, mul_div_mul_left _ _ hfac]
  apply (div_eq_div_iff hnk hna).mpr
  simpa only [mul_comm] using hmul.symm

/-- Exact falling-factorial form of the conditional survivor probability. -/
theorem uniform_subset_contains_descFactorial (S A : Finset α) (hAS : A ⊆ S)
    (k : ℕ) (hAk : A.card ≤ k) (hkS : k ≤ S.card) :
    (((S.powersetCard k).filter (fun U => A ⊆ U)).card : ℝ) /
        (S.powersetCard k).card =
      (k.descFactorial A.card : ℝ) / S.card.descFactorial A.card := by
  rw [uniform_subset_contains S A hAS k hAk hkS]
  exact choose_ratio_eq_descFactorial_ratio S.card k A.card hkS hAk

/-- If fewer than `|A|` blocks survive, it is impossible for all the blocks in
`A` to survive. -/
theorem subsets_containing_eq_empty (S A : Finset α) (k : ℕ)
    (hkA : k < A.card) :
    (S.powersetCard k).filter (fun U => A ⊆ U) = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro U hU
  obtain ⟨hU, hAU⟩ := mem_filter.mp hU
  have hUk := (mem_powersetCard.mp hU).2
  have hle := card_le_card hAU
  rw [hUk] at hle
  exact Nat.not_le_of_lt hkA hle

end Kahn.Ordering
