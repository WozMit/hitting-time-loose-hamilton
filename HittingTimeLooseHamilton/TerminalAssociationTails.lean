module

public import HittingTimeLooseHamilton.AssociationSwitching
public import HittingTimeLooseHamilton.PoissonFactorialTail
public import HittingTimeLooseHamilton.FiniteMomentBounds

public section

/-! Conditional pair-degree and low-degree-star estimates for fixed degree sequences. -/
noncomputable section
namespace LooseHamilton
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {r : ℕ} {d : V → ℕ} [Nonempty (FixedDegreeState V r d)]

theorem association_factorial_tail (hr : 3 ≤ r) {y : V} {B : Finset V}
    (hyB : y ∉ B) (hA : 0 < associationSlack r d B) (k : ℕ) :
    (fixedDegreeLaw r d).event (fun F => k ≤ associationStatistic F.val y B) ≤
      (associationRate r d y B)^k / (k.factorial : ℝ) :=
  (association_stochastic_domination hr hyB hA).factorial_tail k

/-- The union of bad ordered pairs has cubic rate, crucial for vanishing after N² pairs. -/
theorem fixed_degree_pair_failure_le (hr : 3 ≤ r) {L : ℝ} (hL : 0 ≤ L)
    (hbound : ∀ u v : V, u ≠ v →
      0 < associationSlack r d {v} ∧ associationRate r d u {v} ≤ L) :
    (fixedDegreeLaw r d).event (fun F => ∃ u v, u ≠ v ∧ 3 ≤ pairDegree F.val u v) ≤
      (Fintype.card V : ℝ)^2 * L^3 / 6 := by
  classical
  let E : V × V → FixedDegreeState V r d → Prop :=
    fun p F => p.1 ≠ p.2 ∧ 3 ≤ pairDegree F.val p.1 p.2
  have hb (p : V × V) : (fixedDegreeLaw r d).event (E p) ≤ L^3/6 := by
    by_cases hp : p.1 = p.2
    · simp only [E,hp,ne_eq,not_true_eq_false,false_and]
      simp [FiniteEntropy.Law.event]
      positivity
    · obtain ⟨hA,hR⟩ := hbound p.1 p.2 hp
      have ht := association_factorial_tail (d := d) hr
        (show p.1 ∉ ({p.2} : Finset V) by simpa using hp) hA 3
      have hm := (fixedDegreeLaw r d).event_mono
        (fun F (h : E p F) => h.2)
      have hh : (associationRate r d p.1 {p.2})^3 ≤ L^3 :=
        pow_le_pow_left₀ (associationRate_nonneg hA) hR 3
      have ht' : (fixedDegreeLaw r d).event
          (fun F => 3 ≤ pairDegree F.val p.1 p.2) ≤
          (associationRate r d p.1 {p.2})^3/6 := by
        convert ht using 1 <;> norm_num [associationStatistic]
      exact hm.trans (ht'.trans (div_le_div_of_nonneg_right hh (by norm_num)))
  have hu := FiniteEntropy.Law.finite_union_bound (fixedDegreeLaw r d) E
  have he : (fun F : FixedDegreeState V r d => ∃ u v, u ≠ v ∧ 3 ≤ pairDegree F.val u v) =
      (fun F => ∃ p, E p F) := by
    funext F
    apply propext
    constructor
    · rintro ⟨u,v,h⟩; exact ⟨(u,v),h⟩
    · rintro ⟨⟨u,v⟩,h⟩; exact ⟨u,v,h⟩
  rw [he]
  calc
    _ ≤ ∑ p, (fixedDegreeLaw r d).event (E p) := hu
    _ ≤ ∑ _p : V × V, L^3/6 := sum_le_sum (fun p _ => hb p)
    _ = _ := by simp [Fintype.card_prod]; ring

/-- After the degree sequence is fixed, its low-degree set is deterministic. -/
theorem fixed_degree_star_failure_le (hr : 3 ≤ r) (B : Finset V) {L : ℝ} (_hL : 0 ≤ L)
    (hbound : ∀ y : V,
      0 < associationSlack r d (B.erase y) ∧ associationRate r d y (B.erase y) ≤ L) :
    (fixedDegreeLaw r d).event (fun F => ∃ y, 2 ≤ associationStatistic F.val y (B.erase y)) ≤
      (Fintype.card V : ℝ) * L^2 / 2 := by
  classical
  have hb (y : V) : (fixedDegreeLaw r d).event
      (fun F => 2 ≤ associationStatistic F.val y (B.erase y)) ≤ L^2/2 := by
    obtain ⟨hA,hR⟩ := hbound y
    have ht := association_factorial_tail (d := d) hr (notMem_erase y B) hA 2
    have hh : (associationRate r d y (B.erase y))^2 ≤ L^2 :=
      pow_le_pow_left₀ (associationRate_nonneg hA) hR 2
    have ht' : (fixedDegreeLaw r d).event
        (fun F => 2 ≤ associationStatistic F.val y (B.erase y)) ≤
        (associationRate r d y (B.erase y))^2/2 := by simpa using ht
    exact ht'.trans (div_le_div_of_nonneg_right hh (by norm_num))
  calc
    _ ≤ ∑ y, (fixedDegreeLaw r d).event
        (fun F => 2 ≤ associationStatistic F.val y (B.erase y)) :=
      FiniteEntropy.Law.finite_union_bound _ _
    _ ≤ ∑ _y : V, L^2/2 := sum_le_sum (fun y _ => hb y)
    _ = _ := by simp; ring
end LooseHamilton
