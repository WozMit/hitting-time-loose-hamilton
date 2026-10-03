module

public import HittingTimeLooseHamilton.FiniteMomentBounds
public import Mathlib.Combinatorics.SetFamily.FourFunctions
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.BigOperators.Group.Finset.Powerset

public section

/-! Independent inclusion of the elements of a finite set. -/
noncomputable section
open scoped BigOperators
open Finset
namespace LooseHamilton.BernoulliSubset
variable {A : Type*} [Fintype A] [DecidableEq A]

/-- Product weights, with separate weights for inclusion and exclusion. -/
@[expose] def weight (x y : A → ℝ) (S : Finset A) : ℝ :=
  (∏ a ∈ S, x a) * ∏ a ∈ (univ \ S), y a

lemma weight_eq_prod (x y : A → ℝ) (S : Finset A) :
    weight x y S = ∏ a, if a ∈ S then x a else y a := by
  rw [Finset.prod_ite]
  simp [weight, filter_mem_eq_inter, sdiff_eq_filter]

lemma sum_weight (x y : A → ℝ) : ∑ S : Finset A, weight x y S = ∏ a, (x a + y a) := by
  simpa [weight] using (Finset.prod_add x y (univ : Finset A)).symm

lemma weight_const (p q : ℝ) (S : Finset A) :
    weight (fun _ => p) (fun _ => q) S = p ^ S.card * q ^ (Fintype.card A - S.card) := by
  simp [weight, card_sdiff_of_subset (subset_univ S)]

/-- Each element is included independently with probability p. -/
@[expose] def law (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) : FiniteEntropy.Law (Finset A) where
  mass := weight (fun _ => p) (fun _ => 1-p)
  nonneg S := by
    rw [weight_const]
    exact mul_nonneg (pow_nonneg hp0 _) (pow_nonneg (sub_nonneg.mpr hp1) _)
  total := by rw [sum_weight]; simp

lemma mass_modular (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (S T : Finset A) :
    (law p hp0 hp1).mass S * (law p hp0 hp1).mass T =
      (law p hp0 hp1).mass (S ∩ T) * (law p hp0 hp1).mass (S ∪ T) := by
  change weight _ _ S * weight _ _ T = weight _ _ _ * weight _ _ _
  simp_rw [weight_eq_prod, ← prod_mul_distrib]
  apply prod_congr rfl
  intro a ha
  by_cases hS : a ∈ S <;> by_cases hT : a ∈ T <;> simp [hS,hT,mul_comm]

/-- Positive association for increasing events under independent inclusion. -/
theorem positive_association (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (E F : Finset A → Prop) (hE : Monotone E) (hF : Monotone F) :
    (law p hp0 hp1).event E * (law p hp0 hp1).event F ≤
      (law p hp0 hp1).event (fun S => E S ∧ F S) := by
  classical
  let f : Finset A → ℝ := fun S => if E S then 1 else 0
  let g : Finset A → ℝ := fun S => if F S then 1 else 0
  have hf : Monotone f := by
    intro S T hST
    by_cases h : E S
    · simp [f,h,hE hST h]
    · simp only [f,h,if_false]; split_ifs <;> norm_num
  have hg : Monotone g := by
    intro S T hST
    by_cases h : F S
    · simp [g,h,hF hST h]
    · simp only [g,h,if_false]; split_ifs <;> norm_num
  have h := fkg (μ := (law p hp0 hp1).mass) (f := f) (g := g)
    (fun S => (law p hp0 hp1).nonneg S)
    (fun S => by dsimp [f]; split_ifs <;> norm_num)
    (fun S => by dsimp [g]; split_ifs <;> norm_num) hf hg
    (fun S T => (mass_modular p hp0 hp1 S T).le)
  rw [(law p hp0 hp1).total, one_mul] at h
  have hmean (P : Finset A → Prop) :
      (∑ S, (law p hp0 hp1).mass S * (if P S then (1:ℝ) else 0)) =
        (law p hp0 hp1).event P := by
    unfold FiniteEntropy.Law.event
    apply sum_congr rfl
    intro S hS
    by_cases hh : P S <;> simp [hh]
  have hfg : (∑ S, (law p hp0 hp1).mass S * (f S * g S)) =
      (law p hp0 hp1).event (fun S => E S ∧ F S) := by
    unfold FiniteEntropy.Law.event
    apply sum_congr rfl
    intro S hS
    by_cases he : E S <;> by_cases hf : F S <;> simp [f,g,he,hf]
  rw [hfg] at h
  change (∑ S, _ * (if E S then (1:ℝ) else 0)) *
    (∑ S, _ * (if F S then (1:ℝ) else 0)) ≤ _ at h
  rw [hmean,hmean] at h
  exact h

/-- A finite family of increasing events has at least its product probability. -/
theorem intersection_lower_bound {I : Type*} (T : Finset I)
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (E : I → Finset A → Prop)
    (hE : ∀ i, Monotone (E i)) :
    (∏ i ∈ T, (law p hp0 hp1).event (E i)) ≤
      (law p hp0 hp1).event (fun S => ∀ i ∈ T, E i S) := by
  classical
  induction T using Finset.induction_on with
  | empty => simp
  | @insert i T hi ih =>
    rw [prod_insert hi]
    calc
      _ ≤ (law p hp0 hp1).event (E i) *
          (law p hp0 hp1).event (fun S => ∀ j ∈ T, E j S) :=
        mul_le_mul_of_nonneg_left ih ((law p hp0 hp1).event_nonneg _)
      _ ≤ (law p hp0 hp1).event (fun S => E i S ∧ ∀ j ∈ T, E j S) :=
        positive_association p hp0 hp1 _ _ (hE i) (by
          intro S U hSU h j hj; exact hE j hSU (h j hj))
      _ = _ := by simp

/-- Exact probability-generating function for a support intersection. -/
theorem intersection_moment (p q : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (D : Finset A) :
    (law p hp0 hp1).finiteMean (fun S => q ^ (S ∩ D).card) =
      (1-p+p*q) ^ D.card := by
  have hterm (S : Finset A) :
      (law p hp0 hp1).mass S * q ^ (S ∩ D).card =
      weight (fun a => if a ∈ D then p*q else p) (fun _ => 1-p) S := by
    change weight _ _ S * _ = _
    have hq : q ^ (S ∩ D).card = ∏ a, if a ∈ S ∩ D then q else 1 := by
      rw [Fintype.prod_ite_mem]; simp
    rw [hq]
    simp_rw [weight_eq_prod, ← prod_mul_distrib]
    apply prod_congr rfl
    intro a ha
    by_cases hS : a ∈ S <;> by_cases hD : a ∈ D <;> simp [hS,hD]
  simp_rw [FiniteEntropy.Law.finiteMean,hterm]
  rw [sum_weight]
  calc
    _ = ∏ a, if a ∈ D then (1-p+p*q) else 1 := by
      apply prod_congr rfl
      intro a ha
      by_cases h : a ∈ D <;> simp [h] <;> ring
    _ = _ := by rw [Fintype.prod_ite_mem]; simp

end LooseHamilton.BernoulliSubset
