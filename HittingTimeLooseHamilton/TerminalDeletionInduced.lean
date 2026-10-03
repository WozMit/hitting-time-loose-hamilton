module

public import HittingTimeLooseHamilton.TerminalDeletionDeficit
public import HittingTimeLooseHamilton.CoreTerminalUniform
public import HittingTimeLooseHamilton.CoreRestrictionDegrees

public section

noncomputable section
namespace LooseHamilton
open Finset
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]

lemma vertexDegree_deleteVertices (F : SimpleHypergraph V) (Z : Finset V)
    (v : ↥(univ \ Z)) :
    vertexDegree (deleteVertices Z F) v = vertexDegree (survivingHost F Z) v.val := by
  have heq : survivingHost F Z = coreOutside Z F := by
    rfl
  rw [heq, deleteVertices, ← restricted_core_eq_inducedHost]
  apply vertexDegree_restrictEdges
  intro e he x hx
  exact mem_sdiff.mpr ⟨mem_univ _, fun hz =>
    disjoint_left.mp ((mem_coreOutside _ _ _).mp he).2 hx hz⟩

/-- The deletion estimate expressed on the actual induced subtype. -/
theorem terminal_induced_deletion_deficit (F : SimpleHypergraph V) (ell : V → ℕ)
    (B Z : Finset V)
    (hell : ∀ v, ell v ≤ vertexDegree F v)
    (hslack : ∀ v ∉ B, ell v + 2 * Z.card ≤ vertexDegree F v)
    (hpair : ∀ v y, v ≠ y → pairDegree F v y ≤ 2)
    (hassoc : ∀ y, associationStatistic F y (B.erase y) ≤ 1) :
    (∑ v : ↥(univ \ Z), (ell v.val - vertexDegree (deleteVertices Z F) v)) ≤ Z.card := by
  simp_rw [vertexDegree_deleteVertices]
  rw [Finset.sum_coe_sort (univ \ Z) (fun v => ell v - vertexDegree (survivingHost F Z) v)]
  exact terminal_deletion_deficit F ell B Z hell hslack hpair hassoc

/-- A real low-degree threshold gives the slack required for every bounded deletion. -/
theorem terminal_induced_deletion_deficit_of_threshold (F : SimpleHypergraph V)
    (ell : V → ℕ) (T : ℝ) (h : ℕ)
    (hell : ∀ v, ell v ≤ vertexDegree F v)
    (hslack : ∀ v, (ell v + 2 * h : ℕ) ≤ T)
    (hpair : ∀ v y, v ≠ y → pairDegree F v y ≤ 2)
    (hassoc : ∀ y, associationStatistic F y
      ((univ.filter (fun v => (vertexDegree F v : ℝ) ≤ T)).erase y) ≤ 1)
    (Z : Finset V) (hZ : Z.card ≤ h) :
    (∑ v : ↥(univ \ Z), (ell v.val - vertexDegree (deleteVertices Z F) v)) ≤ Z.card := by
  apply terminal_induced_deletion_deficit F ell
    (univ.filter (fun v => (vertexDegree F v : ℝ) ≤ T)) Z hell _ hpair hassoc
  intro v hv
  have hv' : T < (vertexDegree F v : ℝ) := by simpa using hv
  have hs := hslack v
  have hn : (ell v + 2 * h : ℕ) ≤ vertexDegree F v := by exact_mod_cast (le_of_lt (lt_of_le_of_lt hs hv'))
  omega

end LooseHamilton
