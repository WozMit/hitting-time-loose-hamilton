module

public import HittingTimeLooseHamilton.AssociationModels
public import Mathlib

public section

noncomputable section
namespace LooseHamilton
open Finset
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The edges of the induced hypergraph after deleting `Z`, retaining ambient labels. -/
@[expose] def survivingHost (F : SimpleHypergraph V) (Z : Finset V) : SimpleHypergraph V :=
  F.filter (fun e => Disjoint e Z)

lemma deletion_degree_loss_le (F : SimpleHypergraph V) (Z : Finset V) (v : V) :
    vertexDegree F v - vertexDegree (survivingHost F Z) v ≤
      ∑ y ∈ Z, pairDegree F v y := by
  classical
  have hpoint : ∀ e ∈ F, (if v ∈ e then 1 else 0 : ℕ) ≤
      (if v ∈ e ∧ Disjoint e Z then 1 else 0) +
        ∑ y ∈ Z, if v ∈ e ∧ y ∈ e then 1 else 0 := by
    intro e he
    by_cases hv : v ∈ e
    · by_cases hd : Disjoint e Z
      · simp [hv, hd]
      · obtain ⟨y, hy, hyZ⟩ := Finset.not_disjoint_iff.mp hd
        have hi : (1 : ℕ) ≤ ∑ y ∈ Z, if v ∈ e ∧ y ∈ e then 1 else 0 := by
          exact (by simpa [hv, hy] using
            (Finset.single_le_sum (fun y hy => Nat.zero_le (if v ∈ e ∧ y ∈ e then 1 else 0)) hyZ))
        simpa [hv, hd] using hi
    · simp [hv]
  have hs := Finset.sum_le_sum hpoint
  simp only [Finset.sum_add_distrib] at hs
  rw [Finset.sum_comm] at hs
  have hd : vertexDegree (survivingHost F Z) v =
      ∑ e ∈ F, if v ∈ e ∧ Disjoint e Z then 1 else 0 := by
    simp only [vertexDegree, survivingHost, Finset.filter_filter, Finset.sum_boole];
    congr 2; ext e; simp [and_comm]
  have hp : (∑ y ∈ Z, pairDegree F v y) =
      ∑ y ∈ Z, ∑ e ∈ F, if v ∈ e ∧ y ∈ e then 1 else 0 := by
    simp only [pairDegree, Finset.sum_boole, Nat.cast_id]
  rw [← hd, ← hp] at hs
  have hv : vertexDegree F v = ∑ e ∈ F, if v ∈ e then 1 else 0 := by
    simp only [vertexDegree, Finset.sum_boole, Nat.cast_id]
  rw [← hv] at hs
  omega

lemma pairDegree_symm (F : SimpleHypergraph V) (v y : V) :
    pairDegree F v y = pairDegree F y v := by
  simp only [pairDegree, and_comm]

/-- The deterministic deficit estimate in Proposition 4.3. Natural subtraction
is precisely the positive part appearing in the manuscript. -/
theorem terminal_deletion_deficit (F : SimpleHypergraph V) (ell : V → ℕ)
    (B Z : Finset V)
    (hell : ∀ v, ell v ≤ vertexDegree F v)
    (hslack : ∀ v ∉ B, ell v + 2 * Z.card ≤ vertexDegree F v)
    (hpair : ∀ v y, v ≠ y → pairDegree F v y ≤ 2)
    (hassoc : ∀ y, associationStatistic F y (B.erase y) ≤ 1) :
    (∑ v ∈ (univ \ Z), (ell v - vertexDegree (survivingHost F Z) v)) ≤ Z.card := by
  classical
  have hout : ∀ v ∉ Z, v ∉ B → ell v - vertexDegree (survivingHost F Z) v = 0 := by
    intro v hvZ hvB
    have hl := deletion_degree_loss_le F Z v
    have hb : (∑ y ∈ Z, pairDegree F v y) ≤ 2 * Z.card := by
      calc
        _ ≤ ∑ y ∈ Z, 2 := Finset.sum_le_sum (fun y hy => hpair v y (by
          intro he; subst y; exact hvZ hy))
        _ = _ := by simp [Nat.mul_comm]
    have hs := hslack v hvB
    have he := hell v
    omega
  calc
    _ ≤ ∑ v ∈ (univ \ Z), if v ∈ B then ∑ y ∈ Z, pairDegree F y v else 0 := by
      apply Finset.sum_le_sum
      intro v hv
      have hvZ : v ∉ Z := (Finset.mem_sdiff.mp hv).2
      by_cases hvB : v ∈ B
      · simp only [hvB, if_true]
        have hl := deletion_degree_loss_le F Z v
        have he := hell v
        simp only [pairDegree_symm F v] at hl
        omega
      · simp [hvB, hout v hvZ hvB]
    _ = ∑ y ∈ Z, ∑ v ∈ (univ \ Z), if v ∈ B then pairDegree F y v else 0 := by
      calc
        _ = ∑ v ∈ (univ \ Z), ∑ y ∈ Z, if v ∈ B then pairDegree F y v else 0 := by
          apply Finset.sum_congr rfl
          intro v hv
          by_cases hb : v ∈ B <;> simp [hb]
        _ = _ := Finset.sum_comm
    _ ≤ ∑ y ∈ Z, associationStatistic F y (B.erase y) := by
      apply Finset.sum_le_sum
      intro y hy
      unfold associationStatistic
      rw [← Finset.sum_filter]
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro v hv
        simp only [Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ, true_and] at hv
        exact Finset.mem_erase.mpr ⟨by intro h; subst v; exact hv.1 hy, hv.2⟩
      · intros; exact Nat.zero_le _
    _ ≤ ∑ y ∈ Z, 1 := Finset.sum_le_sum (fun y hy => hassoc y)
    _ = _ := by simp

end LooseHamilton
