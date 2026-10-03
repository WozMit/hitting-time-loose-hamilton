module

public import HittingTimeLooseHamilton.AssociationStatement
public import HittingTimeLooseHamilton.NatLawAtoms
public import HittingTimeLooseHamilton.PoissonComparison

public section

/-! Exact uniform degree-layer probabilities and their Poisson comparison. -/
noncomputable section
namespace LooseHamilton
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (r : ℕ) (d : V → ℕ) [Nonempty (FixedDegreeState V r d)]

@[expose] def associationAtom (y : V) (B : Finset V) (t : ℕ) : ℝ :=
  natLawAtom (fixedDegreeLaw r d) (fun F => associationStatistic F.val y B) t

lemma associationAtom_nonneg (y : V) (B : Finset V) (t : ℕ) :
    0 ≤ associationAtom r d y B t := natLawAtom_nonneg _ _ _

lemma associationAtom_eq_count (y : V) (B : Finset V) (t : ℕ) :
    associationAtom r d y B t =
      (Fintype.card {F : FixedDegreeState V r d // associationStatistic F.val y B=t} : ℝ) /
        Fintype.card (FixedDegreeState V r d) := by
  classical
  unfold associationAtom natLawAtom fixedDegreeLaw
  rw [FiniteEntropy.Law.uniform_event]
  congr 1
  simp [Fintype.card_subtype]

lemma associationAtom_total (y : V) (B : Finset V) :
    ∑ q ∈ range (degreeOn d B+1), associationAtom r d y B q = 1 :=
  sum_natLawAtom_total _ _ _ (fun F => associationStatistic_le_degreeOn F y B)

lemma associationAtom_zero_above (y : V) (B : Finset V) {q : ℕ}
    (hq : degreeOn d B < q) : associationAtom r d y B q = 0 :=
  natLawAtom_eq_zero _ _ _ (fun F => associationStatistic_le_degreeOn F y B) hq

/-- Reusable probability step; the graph-counting modules discharge its birth-rate
inequality for the exact fixed-degree family in the final switching theorem. -/
lemma associationPoisson_of_atom_recurrence (y : V) (B : Finset V)
    (hA : 0 < associationSlack r d B)
    (hrec : ∀ q : ℕ, (q+1 : ℝ)*associationAtom r d y B (q+1) ≤
      associationRate r d y B*associationAtom r d y B q) :
    PoissonDominated (fixedDegreeLaw r d) (fun F => associationStatistic F.val y B)
      ⟨associationRate r d y B,associationRate_nonneg hA⟩ := by
  intro k
  have h := finite_poisson_cdf_le_pmf (associationAtom r d y B)
    ⟨associationRate r d y B,associationRate_nonneg hA⟩ (degreeOn d B) k
    (associationAtom_nonneg r d y B) (fun q hq => associationAtom_zero_above r d y B hq)
    (associationAtom_total r d y B) hrec
  rw [event_ge_eq_one_sub_atoms]
  exact sub_le_sub_left h 1
end LooseHamilton
