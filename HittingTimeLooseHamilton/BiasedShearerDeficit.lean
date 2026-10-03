module

public import HittingTimeLooseHamilton.BiasedShearerCover
public import HittingTimeLooseHamilton.KahnHistory

public section

open scoped BigOperators
noncomputable section
namespace LooseHamilton
open FiniteEntropy
variable {Ω V B : Type*} [Fintype Ω] [Fintype V] [DecidableEq V] [Fintype B]

lemma coordinateEntropy_empty (p : Law Ω) (X : Ω → V → B) :
    coordinateEntropy p X ∅ = 0 := by
  have he : (fun ω => coordinateMask (∅ : Finset V) (X ω)) =
      (fun _ : Ω => fun _ : V => (none : Option B)) := by
    funext ω v
    simp [coordinateMask]
  unfold coordinateEntropy
  rw [he]
  exact p.entropy_map_const _

lemma coordinateEntropy_insert_le (p : Law Ω) (X : Ω → V → B)
    (s : Finset V) (v : V) (hv : v ∉ s) :
    coordinateEntropy p X (insert v s) ≤ coordinateEntropy p X s +
      entropy (p.map (fun ω => some (X ω v))).mass := by
  have hd := coordinateEntropy_diminishing p X ∅ s (Finset.empty_subset _) v hv
  have he := coordinateEntropy_insert p X ∅ v (Finset.notMem_empty _)
  have hc := p.entropy_map_pair_le (fun ω => some (X ω v))
    (fun ω => coordinateMask ∅ (X ω))
  have hh := p.entropy_map_pair (fun ω => some (X ω v))
    (fun ω => coordinateMask ∅ (X ω))
  change _ ≤ _ + coordinateEntropy p X ∅ at hc
  rw [hh] at hc
  change coordinateEntropy p X ∅ + _ ≤ _ + coordinateEntropy p X ∅ at hc
  rw [coordinateEntropy_empty] at hc
  rw [coordinateEntropy_empty] at hd he
  linarith

/-- Cross entropy minus marginal entropy, written additively by coordinates. -/
@[expose] def coordinateDeficit (p : Law Ω) (X : Ω → V → B) (c : V → ℝ) (s : Finset V) : ℝ :=
  (∑ v ∈ s, c v) - coordinateEntropy p X s

lemma coordinateDeficit_empty (p : Law Ω) (X : Ω → V → B) (c : V → ℝ) :
    coordinateDeficit p X c ∅ = 0 := by
  simp [coordinateDeficit, coordinateEntropy_empty]

lemma coordinateDeficit_insert_nonneg (p : Law Ω) (X : Ω → V → B) (c : V → ℝ)
    (hc : ∀ v, entropy (p.map (fun ω => some (X ω v))).mass ≤ c v)
    (s : Finset V) (v : V) (hv : v ∉ s) :
    coordinateDeficit p X c s ≤ coordinateDeficit p X c (insert v s) := by
  have hh := coordinateEntropy_insert_le p X s v hv
  have hc' := hc v
  simp only [coordinateDeficit, Finset.sum_insert hv]
  linarith

lemma coordinateDeficit_mono (p : Law Ω) (X : Ω → V → B) (c : V → ℝ)
    (hc : ∀ v, entropy (p.map (fun ω => some (X ω v))).mass ≤ c v) :
    Monotone (coordinateDeficit p X c) := by
  intro s t hst
  have haux : ∀ u : Finset V, coordinateDeficit p X c s ≤ coordinateDeficit p X c (s ∪ u) := by
    intro u
    induction u using Finset.induction_on with
    | empty => simp
    | @insert v u hv ih =>
      rw [Finset.union_insert]
      by_cases hmem : v ∈ s ∪ u
      · simpa [Finset.insert_eq_of_mem hmem] using ih
      · exact ih.trans (coordinateDeficit_insert_nonneg p X c hc _ _ hmem)
  simpa [Finset.union_eq_right.mpr hst] using haux t

lemma coordinateDeficit_increasing (p : Law Ω) (X : Ω → V → B) (c : V → ℝ)
    (s t : Finset V) (hst : s ⊆ t) (v : V) (hv : v ∉ t) :
    coordinateDeficit p X c (insert v s) - coordinateDeficit p X c s ≤
      coordinateDeficit p X c (insert v t) - coordinateDeficit p X c t := by
  have hh := coordinateEntropy_diminishing p X s t hst v hv
  simp only [coordinateDeficit, Finset.sum_insert hv,
    Finset.sum_insert (show v ∉ s from fun h => hv (hst h))]
  linarith

/-- Shearer's relative entropy inequality for any coordinate cross entropy costs.
The costs need only dominate their singleton entropies. -/
theorem coordinateDeficit_bounded_degree_sum {I : Type*} [Fintype I]
    (p : Law Ω) (X : Ω → V → B) (c : V → ℝ)
    (hc : ∀ v, entropy (p.map (fun ω => some (X ω v))).mass ≤ c v)
    (e : I → Finset V) (D : ℝ) (hD : 0 ≤ D)
    (hdeg : ∀ v, (∑ i, if v ∈ e i then (1 : ℝ) else 0) ≤ D) :
    ∑ i, coordinateDeficit p X c (e i) ≤ D * coordinateDeficit p X c Finset.univ := by
  exact supermodular_bounded_degree_sum _ (coordinateDeficit_empty p X c)
    (coordinateDeficit_mono p X c hc) (coordinateDeficit_increasing p X c)
    Finset.univ e D hD (fun _ => Finset.subset_univ _) hdeg

end LooseHamilton
