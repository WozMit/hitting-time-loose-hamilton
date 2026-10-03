module

public import HittingTimeLooseHamilton.AssociationModels
public import HittingTimeLooseHamilton.Operations

public section

/-! Exact terminal regularity event of Proposition 4.3. -/
noncomputable section
namespace LooseHamilton
open Finset
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]
attribute [local instance] Classical.propDecidable

/-- The paper's low-degree set, as a function of the fixed degree sequence. -/
@[expose] def terminalLowDegreeSet (d : V → ℕ) : Finset V :=
  univ.filter (fun v => (d v:ℝ) ≤ 3*epsilon*Real.log (Fintype.card V:ℝ))

/-- B_* from Proposition 4.3: the threshold is the real number 3 epsilon log N. -/
@[expose] def terminalLowVertices (F : SimpleHypergraph V) : Finset V :=
  terminalLowDegreeSet (vertexDegree F)

@[simp] theorem mem_terminalLowDegreeSet (d : V → ℕ) (v : V) :
    v ∈ terminalLowDegreeSet d ↔ (d v:ℝ) ≤ 3*epsilon*Real.log (Fintype.card V:ℝ) := by
  simp [terminalLowDegreeSet]

@[simp] theorem mem_terminalLowVertices (F : SimpleHypergraph V) (v : V) :
    v ∈ terminalLowVertices F ↔ (vertexDegree F v:ℝ) ≤
      3*epsilon*Real.log (Fintype.card V:ℝ) := by
  simp [terminalLowVertices]

/-- The four simultaneous terminal regularity bounds in (eq:terminal).
Codegrees are required only for distinct vertices. The star statistic counts
incidences, as in the manuscript, and the root is removed from the low set. -/
structure TerminalRegular (C : ℝ) (F : SimpleHypergraph V) : Prop where
  maximum_degree : ∀ v, (vertexDegree F v:ℝ) ≤ C*Real.log (Fintype.card V:ℝ)
  low_set : ((terminalLowVertices F).card:ℝ) ≤ (Fintype.card V:ℝ)^(1/4:ℝ)
  pair_degree : ∀ u v, u ≠ v → pairDegree F u v ≤ 2
  low_stars : ∀ y, associationStatistic F y ((terminalLowVertices F).erase y) ≤ 1

/-- Total positive degree deficit after deleting Z, using the existing induced
hypergraph on the surviving vertex subtype. Natural subtraction is positive part. -/
@[expose] def terminalDeletionDeficit (F : SimpleHypergraph V) (ell : V → ℕ) (Z : Finset V) : ℕ :=
  ∑ v : ↥(univ \ Z), (ell v.val - vertexDegree (deleteVertices Z F) v)

/-- The maximum-degree and low-set bounds depend only on the degree sequence. -/
@[expose] def TerminalDegreeControls (C : ℝ) (d : V → ℕ) : Prop :=
  (∀ v, (d v:ℝ) ≤ C*Real.log (Fintype.card V:ℝ)) ∧
    ((terminalLowDegreeSet d).card:ℝ) ≤ (Fintype.card V:ℝ)^(1/4:ℝ)

lemma terminalLowVertices_fixedDegree {r : ℕ} {d : V → ℕ}
    (F : FixedDegreeState V r d) : terminalLowVertices F.val = terminalLowDegreeSet d := by
  unfold terminalLowVertices
  congr 1
  funext v
  exact F.property.2 v
end LooseHamilton
