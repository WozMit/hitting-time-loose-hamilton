module

public import HittingTimeLooseHamilton.BiasedShearerBernoulli

public section

open scoped BigOperators
noncomputable section
namespace LooseHamilton
open FiniteEntropy
variable {Ω V B : Type*} [Fintype Ω] [Fintype V] [DecidableEq V] [Fintype B]

lemma coordinateEntropy_univ (p : Law Ω) (X : Ω → V → B) :
    coordinateEntropy p X Finset.univ = entropy (p.map X).mass := by
  have h := (p.map X).entropy_map_of_injective
    (fun x : V → B => fun v => some (x v)) (by
      intro x y h
      funext v
      exact Option.some.inj (congrFun h v))
  rw [Law.map_map] at h
  change entropy (p.map (fun ω => coordinateMask Finset.univ (X ω))).mass = _
  have hf : (fun ω => coordinateMask Finset.univ (X ω)) =
      ((fun x : V → B => fun v => some (x v)) ∘ X) := by
    funext ω v
    simp [coordinateMask, Function.comp_def]
  rw [hf]
  exact h

/-- The cross entropy is constant on binary configurations with a fixed number
of selected coordinates. -/
lemma bernoulli_crossEntropy_fixed_count (p : Law Ω) (X : Ω → V → Bool)
    (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (k : ℕ)
    (hk : ∀ ω, (Finset.univ.filter (fun v => X ω v = true)).card = k) :
    (∑ v, coordinateCrossEntropy p X (fun _ => bernoulliBitLaw a ha0 ha1) v) =
      -((k : ℝ) * Real.log a + ((Fintype.card V-k : ℕ) : ℝ) * Real.log (1-a)) := by
  classical
  have hpoint (ω : Ω) : (∑ v, Real.log ((bernoulliBitLaw a ha0 ha1).mass (X ω v))) =
      (k:ℝ)*Real.log a + ((Fintype.card V-k : ℕ):ℝ)*Real.log (1-a) := by
    change (∑ v, Real.log (if X ω v then a else 1-a)) = _
    simp_rw [apply_ite Real.log]
    rw [Finset.sum_ite]
    simp only [Finset.sum_const, nsmul_eq_mul]
    rw [hk]
    have hc : (Finset.univ.filter (fun v => ¬X ω v = true)).card = Fintype.card V-k := by
      have hpart := Finset.card_filter_add_card_filter_not (s := Finset.univ)
        (p := fun v => X ω v = true)
      rw [hk, Finset.card_univ] at hpart
      omega
    rw [hc]
  simp only [coordinateCrossEntropy, Finset.sum_neg_distrib]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, hpoint]
  rw [← Finset.sum_mul, p.total, one_mul]

/-- The global Bernoulli relative entropy deficit for a fixed-size random set. -/
theorem bernoulli_deficit_fixed_count (p : Law Ω) (X : Ω → V → Bool)
    (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (k : ℕ)
    (hk : ∀ ω, (Finset.univ.filter (fun v => X ω v = true)).card = k) :
    coordinateDeficit p X (coordinateCrossEntropy p X
      (fun _ => bernoulliBitLaw a ha0 ha1)) Finset.univ =
      -((k:ℝ)*Real.log a + ((Fintype.card V-k : ℕ):ℝ)*Real.log (1-a)) -
        entropy (p.map X).mass := by
  rw [coordinateDeficit, bernoulli_crossEntropy_fixed_count p X a ha0 ha1 k hk,
    coordinateEntropy_univ]

end LooseHamilton
