module

public import HittingTimeLooseHamilton.BiasedShearerDeficit

public section

open scoped BigOperators
noncomputable section
namespace LooseHamilton
open FiniteEntropy
variable {Ω V B : Type*} [Fintype Ω] [Fintype V] [DecidableEq V] [Fintype B]

/-- Cross entropy against an independent coordinate reference. -/
@[expose] def coordinateCrossEntropy (p : Law Ω) (X : Ω → V → B) (q : V → Law B) (v : V) : ℝ :=
  -∑ ω, p.mass ω * Real.log ((q v).mass (X ω v))

lemma coordinateEntropy_singleton_le_crossEntropy (p : Law Ω) (X : Ω → V → B)
    (q : V → Law B) (hq : ∀ v b, 0 < (q v).mass b) (v : V) :
    entropy (p.map (fun ω => some (X ω v))).mass ≤ coordinateCrossEntropy p X q v := by
  have hi := (p.map (fun ω => X ω v)).entropy_map_of_injective
    (some : B → Option B) (Option.some_injective B)
  rw [Law.map_map] at hi
  change entropy (p.map (fun ω => some (X ω v))).mass = _ at hi
  rw [hi]
  have he := entropy_le_crossEntropy (p.map (fun ω => X ω v)) (q v) (hq v)
  rw [Law.sum_map_mul] at he
  exact he

/-- Relative entropy Shearer inequality in additive cross entropy form.
All reference coordinates may have different positive laws. -/
theorem crossEntropy_deficit_bounded_degree_sum {I : Type*} [Fintype I]
    (p : Law Ω) (X : Ω → V → B) (q : V → Law B)
    (hq : ∀ v b, 0 < (q v).mass b)
    (e : I → Finset V) (D : ℝ) (hD : 0 ≤ D)
    (hdeg : ∀ v, (∑ i, if v ∈ e i then (1 : ℝ) else 0) ≤ D) :
    ∑ i, coordinateDeficit p X (coordinateCrossEntropy p X q) (e i) ≤
      D * coordinateDeficit p X (coordinateCrossEntropy p X q) Finset.univ := by
  exact coordinateDeficit_bounded_degree_sum p X _
    (coordinateEntropy_singleton_le_crossEntropy p X q hq) e D hD hdeg

end LooseHamilton
