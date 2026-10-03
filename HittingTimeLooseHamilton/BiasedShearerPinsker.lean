module

public import HittingTimeLooseHamilton.BiasedShearerProduct
public import HittingTimeLooseHamilton.BiasedPinsker

public section

open scoped BigOperators
noncomputable section
namespace LooseHamilton
open FiniteEntropy
variable {Ω V B I : Type*} [Fintype Ω] [Fintype V] [DecidableEq V]
  [Fintype B] [Nonempty B] [Fintype I]

/-- Sum of the full variation errors in the coordinate marginals. -/
@[expose] def coordinateMarginalError (p : Law Ω) (X : Ω → V → B) (q : V → Law B)
    (s : Finset V) : ℝ :=
  ∑ x : s → B, |(coordinateRestrictionLaw p X s).mass x -
    (independentCoordinateLaw (fun v : s => q v.val)).mass x|

/-- Pinsker and Shearer together control the sum of all marginal errors. -/
theorem coordinateMarginalError_sum_sq (p : Law Ω) (X : Ω → V → B)
    (q : V → Law B) (hq : ∀ v b, 0 < (q v).mass b)
    (e : I → Finset V) (D : ℝ) (hD : 0 ≤ D)
    (hdeg : ∀ v, (∑ i, if v ∈ e i then (1 : ℝ) else 0) ≤ D) :
    (∑ i, coordinateMarginalError p X q (e i))^2 ≤
      4 * (Fintype.card I : ℝ) * D *
        coordinateDeficit p X (coordinateCrossEntropy p X q) Finset.univ := by
  have hi (i : I) : (coordinateMarginalError p X q (e i))^2 ≤
      4 * finiteRelativeEntropy (coordinateRestrictionLaw p X (e i))
        (independentCoordinateLaw (fun v : e i => q v.val)) := by
    simpa only [coordinateMarginalError, finiteRelativeEntropy, entropy, neg_neg,
      Finset.sum_sub_distrib] using l1_sq_le_four_relative_entropy (coordinateRestrictionLaw p X (e i))
      (independentCoordinateLaw (fun v : e i => q v.val))
      (independentCoordinateLaw_pos (fun v : e i => q v.val) (fun v b => hq v.val b))
  have hw := weighted_error_sq_le (fun _ : I => (1:ℝ))
    (fun i => coordinateMarginalError p X q (e i))
    (fun i => finiteRelativeEntropy (coordinateRestrictionLaw p X (e i))
      (independentCoordinateLaw (fun v : e i => q v.val))) (fun _ => by norm_num) hi
  simp only [one_mul, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] at hw
  have hs := relativeEntropy_bounded_degree_sum p X q hq e D hD hdeg
  have hm := mul_le_mul_of_nonneg_left hs (show 0 ≤ 4 * (Fintype.card I : ℝ) by positivity)
  nlinarith

end LooseHamilton
