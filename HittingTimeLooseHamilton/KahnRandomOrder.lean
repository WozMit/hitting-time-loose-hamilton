module

public import HittingTimeLooseHamilton.KahnLaw
public import HittingTimeLooseHamilton.KahnConditionalOrder

public section

open scoped BigOperators

noncomputable section

namespace FiniteEntropy.Law

open Finset

variable {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]

/-- A uniform-law event has exactly its finite cardinality ratio. -/
lemma uniform_event [Nonempty A] (E : A → Prop) [DecidablePred E] :
    (uniform (A := A)).event E =
      ((univ.filter E).card : ℝ) / Fintype.card A := by
  classical
  calc
    (uniform (A := A)).event E = ∑ a ∈ univ.filter E, (Fintype.card A : ℝ)⁻¹ := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro a _
      by_cases h : E a <;> simp [event, uniform, h]
    _ = _ := by simp [div_eq_mul_inv]


/-- Uniform finite sampling is invariant under a bijective change of coordinates. -/
lemma uniform_event_equiv [Nonempty A] [Nonempty B] (e : A ≃ B) (E : B → Prop) :
    (uniform (A := A)).event (fun a => E (e a)) = (uniform (A := B)).event E := by
  classical
  rw [uniform_event, uniform_event, Fintype.card_congr e]
  have h : (univ.filter (fun a => E (e a))).card = (univ.filter E).card :=
    card_equiv e (fun _ => by simp)
  rw [h]

/-- Averaging the conditional event probabilities in a product law. -/
lemma event_prod_sum (p : Law A) (q : Law B) (E : A × B → Prop) :
    (p.prod q).event E = ∑ a, p.mass a * q.event (fun b => E (a, b)) := by
  classical
  unfold event prod
  rw [Fintype.sum_prod_type]
  apply sum_congr rfl
  intro a _
  rw [mul_sum]
  apply sum_congr rfl
  intro b _
  by_cases h : E (a, b) <;> simp [h]

lemma event_const_and (p : Law A) (P : Prop) [Decidable P] (E : A → Prop) :
    p.event (fun a => P ∧ E a) = if P then p.event E else 0 := by
  classical
  by_cases h : P <;> simp [event, h]

lemma event_compl (p : Law A) (E : A → Prop) :
    p.event (fun a => ¬ E a) = 1 - p.event E := by
  classical
  have h : p.event E + p.event (fun a => ¬ E a) = 1 := by
    unfold event
    rw [← sum_add_distrib, ← p.total]
    apply sum_congr rfl
    intro a _
    by_cases ha : E a <;> simp [ha]
  linarith

/-- Independence of events on the two independently sampled coordinates. -/
lemma event_prod_and (p : Law A) (q : Law B) (E : A → Prop) (F : B → Prop) :
    (p.prod q).event (fun z => E z.1 ∧ F z.2) = p.event E * q.event F := by
  classical
  rw [event_prod_sum]
  simp only [event_const_and]
  unfold event
  rw [sum_mul]
  apply sum_congr rfl
  intro a _
  by_cases h : E a <;> simp [h]

/-- If an ordering event has the same probability for each underlying object
satisfying `D`, then conditioning the object on `D` does not change that
ordering probability. The unnormalized formulation also handles null events. -/
lemma event_prod_eq_of_const_on (p : Law A) (q : Law B)
    (D : A → Prop) (E : A → B → Prop) (c : ℝ)
    (hc : ∀ a, D a → q.event (E a) = c) :
    (p.prod q).event (fun z => D z.1 ∧ E z.1 z.2) = p.event D * c := by
  classical
  rw [event_prod_sum]
  simp only [event_const_and]
  unfold event
  rw [sum_mul]
  apply sum_congr rfl
  intro a _
  by_cases h : D a
  · simp only [h, ↓reduceIte]
    rw [← hc a h]
    rfl
  · simp [h]

/-- Mixture upper bound separating exceptional and ordinary objects. This is
the finite-law form of equation (37) in Kahn's paper. -/
lemma event_prod_le_bad_good (p : Law A) (q : Law B)
    (bad : A → Prop) (E : A → B → Prop) (a b : ℝ)
    (hbad : ∀ x, bad x → q.event (E x) ≤ a)
    (hgood : ∀ x, ¬ bad x → q.event (E x) ≤ b) :
    (p.prod q).event (fun z => E z.1 z.2) ≤
      p.event bad * a + (1 - p.event bad) * b := by
  classical
  rw [event_prod_sum]
  calc
    (∑ x, p.mass x * q.event (E x)) ≤
        ∑ x, if bad x then p.mass x * a else p.mass x * b := by
      apply sum_le_sum
      intro x _
      by_cases hx : bad x
      · simp only [hx, ↓reduceIte]
        exact mul_le_mul_of_nonneg_left (hbad x hx) (p.nonneg x)
      · simp only [hx, ↓reduceIte]
        exact mul_le_mul_of_nonneg_left (hgood x hx) (p.nonneg x)
    _ = p.event bad * a + p.event (fun x => ¬ bad x) * b := by
      unfold event
      rw [sum_mul, sum_mul, ← sum_add_distrib]
      apply sum_congr rfl
      intro x _
      by_cases hx : bad x <;> simp [hx]
    _ = p.event bad * a + (1 - p.event bad) * b := by rw [event_compl]

end FiniteEntropy.Law

namespace Kahn.Ordering

open FiniteEntropy

variable {B R L : Type*} [Fintype B] [Fintype R] [Nonempty R]
  [Fintype L] [DecidableEq B] [DecidableEq R] [LinearOrder L]
  [Nonempty ((B × R) ≃ L)]

/-- The joint first-vertex/block-rank count as a probability under the actual
uniform ordering law. -/
theorem uniform_law_blockOrderVertex (k : Fin (Fintype.card B)) (v : B × R) :
    (uniform (A := (B × R) ≃ L)).event (fun σ => blockOrderVertex σ k = v) =
      1 / (Fintype.card B * Fintype.card R) := by
  classical
  rw [Law.uniform_event]
  exact blockOrderVertex_uniform (L := L) k v

/-- The exact survivor calculation as a uniform-law event probability. -/
theorem uniform_law_first_survivor (k : Fin (Fintype.card B))
    (v : B × R) (A : Finset B) (hvA : v.1 ∉ A) :
    (uniform (A := (B × R) ≃ L)).event
      (fun σ => blockOrderVertex σ k = v ∧ A ⊆ laterBlocks σ k) =
      (1 / (Fintype.card B * Fintype.card R) : ℝ) *
        ((Fintype.card B - 1 - k).descFactorial A.card : ℝ) /
          (Fintype.card B - 1).descFactorial A.card := by
  classical
  rw [Law.uniform_event]
  exact first_survivor_probability_descFactorial (L := L) k v A hvA

end Kahn.Ordering
