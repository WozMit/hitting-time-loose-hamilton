module

public import HittingTimeLooseHamilton.AssociationProbability
public import HittingTimeLooseHamilton.AssociationLayerRecurrence

public section

/-! Lemma 4.2, obtained from the exact two-edge switching on the fixed-degree model. -/
noncomputable section
namespace LooseHamilton
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {r : ℕ} {d : V → ℕ} [Nonempty (FixedDegreeState V r d)]

lemma associationAtom_eq_layerCount (y : V) (B : Finset V) (t : ℕ) :
    associationAtom r d y B t = (associationLayerCount r d y B t : ℝ) /
      Fintype.card (FixedDegreeState V r d) := by
  rw [associationAtom_eq_count]
  rfl

/-- The birth-rate inequality is proved for the actual uniform graph law. -/
theorem association_atom_recurrence (hr : 3 ≤ r) {y : V} {B : Finset V}
    (hyB : y ∉ B) (hA : 0 < associationSlack r d B) (q : ℕ) :
    (q+1 : ℝ)*associationAtom r d y B (q+1) ≤
      associationRate r d y B*associationAtom r d y B q := by
  have hc := association_layer_recurrence (d := d) hr hyB (q+1)
  simp only [Nat.add_sub_cancel,Nat.cast_add,Nat.cast_one] at hc
  have hb : (q+1 : ℝ)*(associationLayerCount r d y B (q+1) : ℝ) ≤
      associationRate r d y B*(associationLayerCount r d y B q : ℝ) := by
    unfold associationRate
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hA).mpr
    convert hc using 1 <;> ring
  rw [associationAtom_eq_layerCount,associationAtom_eq_layerCount]
  simpa only [mul_div_assoc] using div_le_div_of_nonneg_right hb
    (Nat.cast_nonneg (Fintype.card (FixedDegreeState V r d)))

/-- Full Poisson stochastic domination of the association statistic, without any
unproved recurrence or regularity hypothesis. -/
theorem association_stochastic_domination (hr : 3 ≤ r) {y : V} {B : Finset V}
    (hyB : y ∉ B) (hA : 0 < associationSlack r d B) :
    PoissonDominated (fixedDegreeLaw r d) (fun F => associationStatistic F.val y B)
      ⟨associationRate r d y B,associationRate_nonneg hA⟩ :=
  associationPoisson_of_atom_recurrence r d y B hA (association_atom_recurrence hr hyB hA)

/-- The conclusion with the full infinite Poisson upper tail displayed. -/
theorem association_poisson_tsum (hr : 3 ≤ r) {y : V} {B : Finset V}
    (hyB : y ∉ B) (hA : 0 < associationSlack r d B) (k : ℕ) :
    (fixedDegreeLaw r d).event (fun F => k ≤ associationStatistic F.val y B) ≤
      ∑' j : ℕ, ProbabilityTheory.poissonPMFReal
        ⟨associationRate r d y B,associationRate_nonneg hA⟩ (j+k) := by
  have h := association_stochastic_domination hr hyB hA k
  exact h.trans_eq (poisson_upper_tail_eq_tsum _ _)

/-- The paper explicitly allows B to depend arbitrarily on the fixed degree
sequence; it is fixed before the random graph is sampled. -/
theorem association_degree_dependent_set (hr : 3 ≤ r)
    (chooseB : (V → ℕ) → Finset V) (y : V) (hyB : y ∉ chooseB d)
    (hA : 0 < associationSlack r d (chooseB d)) :
    PoissonDominated (fixedDegreeLaw r d) (fun F => associationStatistic F.val y (chooseB d))
      ⟨associationRate r d y (chooseB d),associationRate_nonneg hA⟩ :=
  association_stochastic_domination hr hyB hA

/-- Lemma 4.2 (Degree-preserving association switching). -/
theorem lemma42 : Lemma42 := by
  intro N r hN hr d _ y B hyB hA
  exact association_stochastic_domination hr hyB hA
end LooseHamilton
