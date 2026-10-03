module

public import HittingTimeLooseHamilton.Models
public import HittingTimeLooseHamilton.Setup
public import HittingTimeLooseHamilton.KahnRandomOrder

public section

/-! The exact fixed-degree-sequence model and statistic of Lemma 4.2. -/
noncomputable section
namespace LooseHamilton
open Finset
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]
attribute [local instance] Classical.propDecidable

/-- All simple r-graphs with exactly the prescribed degree sequence. -/
@[expose] def FixedDegreeState (V : Type*) [Fintype V] [DecidableEq V]
    (r : ℕ) (d : V → ℕ) :=
  {F : SimpleHypergraph V // F ⊆ completeEdges V r ∧ ∀ v, vertexDegree F v = d v}

@[expose] instance {r : ℕ} {d : V → ℕ} : Fintype (FixedDegreeState V r d) := by
  unfold FixedDegreeState
  infer_instance

@[expose] def fixedDegreeLaw (r : ℕ) (d : V → ℕ) [Nonempty (FixedDegreeState V r d)] :
    FiniteEntropy.Law (FixedDegreeState V r d) := FiniteEntropy.uniform

@[expose] def degreeSum (d : V → ℕ) : ℕ := ∑ v, d v

@[expose] def degreeMaximum (d : V → ℕ) : ℕ := univ.sup d

@[expose] def degreeOn (d : V → ℕ) (B : Finset V) : ℕ := ∑ v ∈ B, d v

@[expose] def associationStatistic (F : SimpleHypergraph V) (y : V) (B : Finset V) : ℕ :=
  ∑ z ∈ B, pairDegree F y z

/-- An edge together with one of its vertices. -/
@[expose] def graphIncidences (F : SimpleHypergraph V) : Finset (Finset V × V) :=
  univ.filter (fun p => p.1 ∈ F ∧ p.2 ∈ p.1)

/-- Source labels (e,z), with y,z in e and z in B. -/
@[expose] def associationSources (F : SimpleHypergraph V) (y : V) (B : Finset V) :
    Finset (Finset V × V) :=
  (graphIncidences F).filter (fun p => y ∈ p.1 ∧ p.2 ∈ B)

@[simp] theorem mem_graphIncidences (F : SimpleHypergraph V) (p : Finset V × V) :
    p ∈ graphIncidences F ↔ p.1 ∈ F ∧ p.2 ∈ p.1 := by simp [graphIncidences]

@[simp] theorem mem_associationSources (F : SimpleHypergraph V) (y : V) (B : Finset V)
    (p : Finset V × V) :
    p ∈ associationSources F y B ↔ p.1 ∈ F ∧ p.2 ∈ p.1 ∧ y ∈ p.1 ∧ p.2 ∈ B := by
  simp only [associationSources,mem_filter,mem_graphIncidences]
  tauto

@[expose] def associationBadBudget (r : ℕ) (d : V → ℕ) (B : Finset V) : ℕ :=
  degreeOn d B + r^2*degreeMaximum d + 2*(degreeMaximum d)^2

/-- The denominator A_B, as a real difference (not truncated subtraction). -/
@[expose] def associationSlack (r : ℕ) (d : V → ℕ) (B : Finset V) : ℝ :=
  (degreeSum d : ℝ)-degreeOn d B-(r : ℝ)^2*degreeMaximum d-2*(degreeMaximum d : ℝ)^2

@[expose] def associationNumerator (r : ℕ) (d : V → ℕ) (y : V) (B : Finset V) : ℕ :=
  (r-1)*d y*degreeOn d B

@[expose] def associationRate (r : ℕ) (d : V → ℕ) (y : V) (B : Finset V) : ℝ :=
  (associationNumerator r d y B : ℝ)/associationSlack r d B

lemma degree_le_maximum (d : V → ℕ) (v : V) : d v ≤ degreeMaximum d :=
  le_sup (mem_univ v)

lemma associationSlack_eq_sub_budget (r : ℕ) (d : V → ℕ) (B : Finset V) :
    associationSlack r d B = (degreeSum d : ℝ)-associationBadBudget r d B := by
  simp only [associationSlack,associationBadBudget,Nat.cast_add,Nat.cast_mul,Nat.cast_pow, Nat.cast_ofNat]
  ring

lemma associationRate_nonneg {r : ℕ} {d : V → ℕ} {y : V} {B : Finset V}
    (hA : 0 < associationSlack r d B) : 0 ≤ associationRate r d y B := by
  exact div_nonneg (Nat.cast_nonneg _) hA.le

lemma associationStatistic_le_degreeOn {r : ℕ} {d : V → ℕ}
    (F : FixedDegreeState V r d) (y : V) (B : Finset V) :
    associationStatistic F.val y B ≤ degreeOn d B := by
  apply sum_le_sum
  intro z hz
  calc
    pairDegree F.val y z ≤ vertexDegree F.val z := by
      apply card_le_card
      intro e he
      obtain ⟨he,hy,hz⟩ := mem_filter.mp he
      exact mem_filter.mpr ⟨he,hz⟩
    _ = d z := F.property.2 z
end LooseHamilton
