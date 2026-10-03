module

public import HittingTimeLooseHamilton.BiasedShearerCrossEntropy
public import HittingTimeLooseHamilton.BiasedCollisionEntropy
public import Mathlib.Algebra.BigOperators.Ring.Finset

public section

open scoped BigOperators
noncomputable section
namespace LooseHamilton
open FiniteEntropy
variable {Ω V B : Type*} [Fintype Ω] [Fintype V] [DecidableEq V] [Fintype B]

/-- Independent finite coordinates, with potentially different reference laws. -/
@[expose] def independentCoordinateLaw (q : V → Law B) : Law (V → B) where
  mass x := ∏ v, (q v).mass (x v)
  nonneg x := Finset.prod_nonneg (fun v _ => (q v).nonneg (x v))
  total := by rw [← Fintype.prod_sum]; simp only [Law.total, Finset.prod_const_one]

lemma independentCoordinateLaw_pos (q : V → Law B) (hq : ∀ v b, 0 < (q v).mass b)
    (x : V → B) : 0 < (independentCoordinateLaw q).mass x :=
  Finset.prod_pos (fun v _ => hq v (x v))

/-- The marginal on a literal finite set of coordinates. -/
@[expose] def coordinateRestrictionLaw (p : Law Ω) (X : Ω → V → B) (s : Finset V) : Law (s → B) :=
  p.map (fun ω v => X ω v.val)

lemma coordinateRestriction_entropy [Nonempty B] (p : Law Ω) (X : Ω → V → B)
    (s : Finset V) :
    entropy (coordinateRestrictionLaw p X s).mass = coordinateEntropy p X s := by
  classical
  let b : B := Classical.choice inferInstance
  apply entropy_eq_of_mutual_determination p
    (fun ω (v : s) => X ω v.val) (fun ω => coordinateMask s (X ω))
    (fun y v => if h : v ∈ s then some (y ⟨v,h⟩) else none)
    (fun y v => (y v.val).getD b)
  · intro ω; funext v
    by_cases hv : v ∈ s <;> simp [coordinateMask, hv]
  · intro ω; funext v
    simp [coordinateMask, v.property]

/-- Exact identification of the additive entropy deficit with the relative
entropy of a marginal against a product reference. -/
theorem coordinateRestriction_relativeEntropy [Nonempty B]
    (p : Law Ω) (X : Ω → V → B) (q : V → Law B)
    (hq : ∀ v b, 0 < (q v).mass b) (s : Finset V) :
    finiteRelativeEntropy (coordinateRestrictionLaw p X s)
      (independentCoordinateLaw (fun v : s => q v.val)) =
        coordinateDeficit p X (coordinateCrossEntropy p X q) s := by
  unfold finiteRelativeEntropy
  rw [coordinateRestriction_entropy]
  change -coordinateEntropy p X s -
    (∑ x, (p.map (fun ω (v : s) => X ω v.val)).mass x *
      Real.log (∏ v : s, (q v.val).mass (x v))) = _
  rw [Law.sum_map_mul]
  have hlog (ω : Ω) : Real.log (∏ v : s, (q v.val).mass (X ω v.val)) =
      ∑ v : s, Real.log ((q v.val).mass (X ω v.val)) :=
    Real.log_prod (fun v _ => (hq v.val _).ne')
  simp_rw [hlog]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  simp only [coordinateDeficit, coordinateCrossEntropy, Finset.sum_neg_distrib]
  rw [Finset.sum_coe_sort s (fun v => ∑ ω, p.mass ω * Real.log ((q v).mass (X ω v)))]
  ring

/-- Relative entropy Shearer inequality against a product reference. -/
theorem relativeEntropy_bounded_degree_sum {I : Type*} [Fintype I] [Nonempty B]
    (p : Law Ω) (X : Ω → V → B) (q : V → Law B)
    (hq : ∀ v b, 0 < (q v).mass b)
    (e : I → Finset V) (D : ℝ) (hD : 0 ≤ D)
    (hdeg : ∀ v, (∑ i, if v ∈ e i then (1 : ℝ) else 0) ≤ D) :
    ∑ i, finiteRelativeEntropy (coordinateRestrictionLaw p X (e i))
      (independentCoordinateLaw (fun v : e i => q v.val)) ≤
      D * coordinateDeficit p X (coordinateCrossEntropy p X q) Finset.univ := by
  simp_rw [coordinateRestriction_relativeEntropy p X q hq]
  exact crossEntropy_deficit_bounded_degree_sum p X q hq e D hD hdeg

end LooseHamilton
