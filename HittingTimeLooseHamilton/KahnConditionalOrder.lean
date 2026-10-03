module

public import HittingTimeLooseHamilton.KahnBlockOrder

public section

namespace Kahn.Ordering

open Finset

/-- Equicardinal fibres over a finite set make every further restriction
uniform. The event `E` need not have positive probability. -/
theorem uniform_refinement_probability {Ω C : Type*} [Fintype Ω] [DecidableEq C]
    (E : Ω → Prop) [DecidablePred E] (f : Ω → C) (s : Finset C) (hs : s.Nonempty)
    (hmap : ∀ ω, E ω → f ω ∈ s)
    (hequal : ∀ a ∈ s, ∀ b ∈ s,
      (univ.filter (fun ω => E ω ∧ f ω = a)).card =
        (univ.filter (fun ω => E ω ∧ f ω = b)).card)
    (P : C → Prop) [DecidablePred P] :
    ((univ.filter (fun ω => E ω ∧ P (f ω))).card : ℝ) / Fintype.card Ω =
      ((univ.filter E).card : ℝ) / Fintype.card Ω *
        ((s.filter P).card : ℝ) / s.card := by
  obtain ⟨b, hb⟩ := hs
  let c := (univ.filter (fun ω => E ω ∧ f ω = b)).card
  have count (t : Finset C) :
      (univ.filter (fun ω => E ω ∧ f ω ∈ t)).card =
        ∑ a ∈ t, (univ.filter (fun ω => E ω ∧ f ω = a)).card := by
    simpa only [filter_filter] using
      (sum_card_fiberwise_eq_card_filter (univ.filter E) t f).symm
  have hE : (univ.filter E).card = s.card * c := by
    calc
      (univ.filter E).card = (univ.filter (fun ω => E ω ∧ f ω ∈ s)).card := by
        congr 1
        ext ω
        simp only [mem_filter, mem_univ, true_and]
        exact ⟨fun h => ⟨h, hmap ω h⟩, And.left⟩
      _ = ∑ a ∈ s, (univ.filter (fun ω => E ω ∧ f ω = a)).card := count s
      _ = s.card * c := sum_const_nat (fun a ha => hequal a ha b hb)
  have hG : (univ.filter (fun ω => E ω ∧ P (f ω))).card = (s.filter P).card * c := by
    calc
      (univ.filter (fun ω => E ω ∧ P (f ω))).card =
          (univ.filter (fun ω => E ω ∧ f ω ∈ s.filter P)).card := by
        congr 1
        ext ω
        simp only [mem_filter, mem_univ, true_and]
        exact ⟨fun h => ⟨h.1, hmap ω h.1, h.2⟩, fun h => ⟨h.1, h.2.2⟩⟩
      _ = ∑ a ∈ s.filter P, (univ.filter (fun ω => E ω ∧ f ω = a)).card := count _
      _ = (s.filter P).card * c :=
        sum_const_nat (fun a ha => hequal a (mem_filter.mp ha).1 b hb)
  have hcross : (univ.filter (fun ω => E ω ∧ P (f ω))).card * s.card =
      (univ.filter E).card * (s.filter P).card := by
    rw [hE, hG]
    ac_rfl
  have hcrossR : ((univ.filter (fun ω => E ω ∧ P (f ω))).card : ℝ) * s.card =
      ((univ.filter E).card : ℝ) * (s.filter P).card := by
    simpa only [Nat.cast_mul] using congrArg (fun n : ℕ => (n : ℝ)) hcross
  have hs0 : (s.card : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (card_ne_zero.mpr ⟨b, hb⟩)
  rw [div_mul_eq_mul_div, div_div, ← hcrossR, mul_div_mul_right _ _ hs0]

variable {B R L : Type*} [Fintype B] [Fintype R] [Nonempty R]
  [Fintype L] [DecidableEq B] [DecidableEq R] [LinearOrder L]

/-- Exact joint survivor probability, before simplifying the subset-count
ratio to falling factorials. -/
theorem first_survivor_probability [Nonempty ((B × R) ≃ L)]
    (k : Fin (Fintype.card B)) (v : B × R) (A : Finset B) :
    ((univ.filter (fun σ : (B × R) ≃ L =>
      blockOrderVertex σ k = v ∧ A ⊆ laterBlocks σ k)).card : ℝ) /
        Fintype.card ((B × R) ≃ L) =
      (1 / (Fintype.card B * Fintype.card R) : ℝ) *
        (((((univ.erase v.1).powersetCard (Fintype.card B - 1 - k)).filter
          (fun T => A ⊆ T)).card : ℝ) /
          ((univ.erase v.1).powersetCard (Fintype.card B - 1 - k)).card) := by
  classical
  let s := (univ.erase v.1).powersetCard (Fintype.card B - 1 - k)
  have hc : (univ.erase v.1 : Finset B).card = Fintype.card B - 1 := by simp
  have hs : s.Nonempty := by
    apply powersetCard_nonempty.mpr
    rw [hc]
    exact Nat.sub_le _ _
  have hmap : ∀ σ : (B × R) ≃ L, blockOrderVertex σ k = v → laterBlocks σ k ∈ s := by
    intro σ hv
    apply mem_powersetCard.mpr
    constructor
    · intro b hb
      apply mem_erase.mpr
      refine ⟨?_, mem_univ _⟩
      intro heq
      subst b
      apply blockOrderVertex_not_mem_laterBlocks σ k
      simpa only [hv] using hb
    · exact card_laterBlocks σ k
  have hequal : ∀ a ∈ s, ∀ b ∈ s,
      (univ.filter (fun σ : (B × R) ≃ L => blockOrderVertex σ k = v ∧
        laterBlocks σ k = a)).card =
      (univ.filter (fun σ : (B × R) ≃ L => blockOrderVertex σ k = v ∧
        laterBlocks σ k = b)).card := by
    intro a ha b hb
    obtain ⟨haS, hac⟩ := mem_powersetCard.mp ha
    obtain ⟨hbS, hbc⟩ := mem_powersetCard.mp hb
    apply card_first_later_eq k v a b (hac.trans hbc.symm)
    · intro hv
      exact notMem_erase v.1 univ (haS hv)
    · intro hv
      exact notMem_erase v.1 univ (hbS hv)
  have hh := uniform_refinement_probability
    (fun σ : (B × R) ≃ L => blockOrderVertex σ k = v)
    (fun σ => laterBlocks σ k) s hs hmap hequal (fun T => A ⊆ T)
  rw [blockOrderVertex_uniform k v] at hh
  simpa only [s, mul_div_assoc] using hh

/-- Equation (38)'s exact joint probability, in falling-factorial form.
`A` is any fixed collection of other blocks; its size need not be at most
the number of surviving blocks. -/
theorem first_survivor_probability_descFactorial [Nonempty ((B × R) ≃ L)]
    (k : Fin (Fintype.card B)) (v : B × R) (A : Finset B) (hvA : v.1 ∉ A) :
    ((univ.filter (fun σ : (B × R) ≃ L =>
      blockOrderVertex σ k = v ∧ A ⊆ laterBlocks σ k)).card : ℝ) /
        Fintype.card ((B × R) ≃ L) =
      (1 / (Fintype.card B * Fintype.card R) : ℝ) *
        ((Fintype.card B - 1 - k).descFactorial A.card : ℝ) /
          (Fintype.card B - 1).descFactorial A.card := by
  classical
  rw [first_survivor_probability]
  have hAS : A ⊆ (univ.erase v.1 : Finset B) := by
    intro b hb
    exact mem_erase.mpr ⟨fun hh => hvA (hh ▸ hb), mem_univ _⟩
  have hc : (univ.erase v.1 : Finset B).card = Fintype.card B - 1 := by simp
  by_cases hAk : A.card ≤ Fintype.card B - 1 - k
  · rw [uniform_subset_contains_descFactorial (univ.erase v.1) A hAS
      (Fintype.card B - 1 - k) hAk (by rw [hc]; exact Nat.sub_le _ _), hc]
    rw [mul_div_assoc]
  · have hlt : Fintype.card B - 1 - k < A.card := Nat.lt_of_not_ge hAk
    rw [subsets_containing_eq_empty _ _ _ hlt, card_empty, Nat.cast_zero, zero_div,
      Nat.descFactorial_eq_zero_iff_lt.mpr hlt, Nat.cast_zero, mul_zero, zero_div]

end Kahn.Ordering
