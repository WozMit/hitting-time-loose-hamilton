module

public import HittingTimeLooseHamilton.KahnConditioning
public import Mathlib.Algebra.BigOperators.Fin

public section

/-! The finite entropy chain rule for an ordered list of observations. -/
open scoped BigOperators
noncomputable section
namespace FiniteEntropy
namespace Law
variable {A B C D : Type*} [Fintype A] [Fintype B] [Fintype C] [Fintype D]

lemma entropy_map_eq_of_factors (p : Law A) (f : A → B) (g : A → C)
    (u : B → C) (v : C → B) (hu : u ∘ f = g) (hv : v ∘ g = f) :
    entropy (p.map f).mass = entropy (p.map g).mass := by
  have h₁ := (p.map f).entropy_map_le u
  have h₂ := (p.map g).entropy_map_le v
  rw [p.map_map, hu] at h₁
  rw [p.map_map, hv] at h₂
  exact le_antisymm h₂ h₁

lemma conditionalMapEntropy_eq_of_factors (p : Law A) (X : A → D)
    (f : A → B) (g : A → C) (u : B → C) (v : C → B)
    (hu : u ∘ f = g) (hv : v ∘ g = f) :
    p.conditionalMapEntropy X f = p.conditionalMapEntropy X g := by
  have ho := p.entropy_map_eq_of_factors f g u v hu hv
  have hp := p.entropy_map_eq_of_factors
    (fun a => (X a, f a)) (fun a => (X a, g a))
    (fun z : D × B => (z.1, u z.2)) (fun z : D × C => (z.1, v z.2))
    (by funext a; exact congrArg (fun z => (X a, z)) (congr_fun hu a))
    (by funext a; exact congrArg (fun z => (X a, z)) (congr_fun hv a))
  have hf := p.entropy_map_pair X f
  have hg := p.entropy_map_pair X g
  linarith

lemma entropy_map_const (p : Law A) (b : B) :
    entropy (p.map (fun _ => b)).mass = 0 := by
  classical
  unfold entropy
  rw [p.sum_map_mul]
  simp [map, event, p.total]

variable {n : ℕ} [Inhabited B]

/-- The values observed before position `k`; later positions have the value `none`. -/
@[expose] def history (X : Fin n → A → B) (k : ℕ) (a : A) : Fin n → Option B :=
  fun i => if i.val < k then some (X i a) else none

/-- Discarding the positions at or after `k` in an already partial observation. -/
@[expose] def mask (k : ℕ) (h : Fin n → Option B) : Fin n → Option B :=
  fun i => if i.val < k then h i else none

/-- Add a newly observed coordinate to the previous history. -/
@[expose] def extendPrefix (i : Fin n) (xh : B × (Fin n → Option B)) : Fin n → Option B :=
  fun j => if j = i then some xh.1 else xh.2 j

/-- Recover a newly observed coordinate and its preceding history. -/
@[expose] def splitPrefix (i : Fin n) (h : Fin n → Option B) : B × (Fin n → Option B) :=
  ((h i).getD default, mask i.val h)

omit [Fintype A] [Fintype B] [Inhabited B] in
lemma extend_prefix (X : Fin n → A → B) (i : Fin n) (a : A) :
    extendPrefix i (X i a, history X i.val a) = history X (i.val + 1) a := by
  funext j
  by_cases hji : j = i
  · subst j
    simp [extendPrefix, history]
  · have hne : j.val ≠ i.val := fun h => hji (Fin.ext h)
    have hlt : j.val < i.val + 1 ↔ j.val < i.val := by omega
    simp [extendPrefix, history, hji, hlt]

omit [Fintype A] [Fintype B] in
lemma split_prefix (X : Fin n → A → B) (i : Fin n) (a : A) :
    splitPrefix i (history X (i.val + 1) a) = (X i a, history X i.val a) := by
  apply Prod.ext
  · simp [splitPrefix, history]
  · funext j
    by_cases hj : j.val < i.val
    · have hj' : j.val < i.val + 1 := by omega
      simp [splitPrefix, mask, history, hj, hj']
    · simp [splitPrefix, mask, history, hj]

lemma entropy_prefix_step (p : Law A) (X : Fin n → A → B) (i : Fin n) :
    entropy (p.map (history X (i.val + 1))).mass -
      entropy (p.map (history X i.val)).mass =
        p.conditionalMapEntropy (X i) (history X i.val) := by
  have heq := p.entropy_map_eq_of_factors
    (fun a => (X i a, history X i.val a)) (history X (i.val + 1))
    (extendPrefix i) (splitPrefix i)
    (funext (extend_prefix X i)) (funext (split_prefix X i))
  have hc := p.entropy_map_pair (X i) (history X i.val)
  linarith

omit [Fintype A] [Fintype B] [Inhabited B] in
lemma prefix_injective (X : Fin n → A → B)
    (hX : Function.Injective (fun a i => X i a)) : Function.Injective (history X n) := by
  intro a b hab
  apply hX
  funext i
  have h := congr_fun hab i
  simpa [history, i.isLt] using h

/-- The full chain rule, valid for any finite law and injective coordinate representation. -/
theorem entropy_ordered_chain (p : Law A) (X : Fin n → A → B)
    (hX : Function.Injective (fun a i => X i a)) :
    entropy p.mass = ∑ i : Fin n, p.conditionalMapEntropy (X i) (history X i.val) := by
  have hzero : entropy (p.map (history X 0)).mass = 0 := by
    have heq : history X 0 = fun _ => (fun _ : Fin n => (none : Option B)) := by
      funext a i
      simp [history]
    rw [heq]
    exact p.entropy_map_const _
  have hfull := p.entropy_map_of_injective (history X n) (prefix_injective X hX)
  have hsum : (∑ i : Fin n, p.conditionalMapEntropy (X i) (history X i.val)) =
      entropy (p.map (history X n)).mass - entropy (p.map (history X 0)).mass := by
    simp_rw [← p.entropy_prefix_step X]
    rw [Fin.sum_univ_eq_sum_range (fun k =>
      entropy (p.map (history X (k + 1))).mass -
        entropy (p.map (history X k)).mass) n]
    exact Finset.sum_range_sub (fun k => entropy (p.map (history X k)).mass) n
  rw [hsum, hzero, sub_zero, hfull]

end Law
end FiniteEntropy
