module

public import HittingTimeLooseHamilton.Models
public import Mathlib.Data.Nat.Choose.Bounds

public section

/-! Broad endpoint-cut labels and their deterministic degree bounds.  The mate
map is arbitrary here: matching legality only narrows these candidate sets. -/
noncomputable section
open Finset
open scoped BigOperators
namespace LooseHamilton
variable {V : Type*} [Fintype V] [DecidableEq V]

@[expose] def endpointCutFirstLabels (H : SimpleHypergraph V) (y : V) :
    Finset (Finset V × V) :=
  (H.filter fun e => y ∈ e).biUnion fun e => (e.erase y).image fun a => (e, a)

@[expose] def endpointCutSecondLabels (H : SimpleHypergraph V) (y : V) (mate : V → V) :
    Finset ((Finset V × V) × (Finset V × V)) :=
  (endpointCutFirstLabels H y).biUnion fun eu =>
    (endpointCutFirstLabels H (mate eu.2)).image fun ea => (eu, ea)

@[simp] theorem mem_endpointCutFirstLabels {H : SimpleHypergraph V} {y : V}
    {e : Finset V} {a : V} :
    (e, a) ∈ endpointCutFirstLabels H y ↔ e ∈ H ∧ y ∈ e ∧ a ∈ e ∧ a ≠ y := by
  simp [endpointCutFirstLabels, and_assoc, and_left_comm, and_comm]

@[simp] theorem mem_endpointCutSecondLabels {H : SimpleHypergraph V} {y : V}
    {mate : V → V} {eu ea : Finset V × V} :
    (eu, ea) ∈ endpointCutSecondLabels H y mate ↔
      eu ∈ endpointCutFirstLabels H y ∧ ea ∈ endpointCutFirstLabels H (mate eu.2) := by
  simp [endpointCutSecondLabels]

theorem endpointCutFirstLabels_card_le {r : ℕ} {H : SimpleHypergraph V}
    (hH : H ⊆ completeEdges V r) (y : V) :
    (endpointCutFirstLabels H y).card ≤ (r - 1) * vertexDegree H y := by
  calc
    _ ≤ ∑ e ∈ H.filter (fun e => y ∈ e), ((e.erase y).image fun a => (e, a)).card :=
      card_biUnion_le
    _ ≤ ∑ e ∈ H.filter (fun e => y ∈ e), (r - 1) := by
      apply sum_le_sum
      intro e he
      have hm := mem_filter.mp he
      have hc := (mem_completeEdges r e).mp (hH hm.1)
      exact (card_image_le).trans (by rw [card_erase_of_mem hm.2, hc])
    _ = _ := by simp [vertexDegree, Nat.mul_comm]

theorem endpointCutSecondLabels_card_le {r Δ : ℕ} {H : SimpleHypergraph V}
    (hH : H ⊆ completeEdges V r) (hΔ : ∀ v, vertexDegree H v ≤ Δ)
    (y : V) (mate : V → V) :
    (endpointCutSecondLabels H y mate).card ≤ (r - 1)^2 * vertexDegree H y * Δ := by
  calc
    _ ≤ ∑ eu ∈ endpointCutFirstLabels H y,
        ((endpointCutFirstLabels H (mate eu.2)).image fun ea => (eu, ea)).card :=
      card_biUnion_le
    _ ≤ ∑ eu ∈ endpointCutFirstLabels H y, (r - 1) * Δ := by
      apply sum_le_sum
      intro eu heu
      exact card_image_le.trans ((endpointCutFirstLabels_card_le hH _).trans
        (Nat.mul_le_mul_left _ (hΔ _)))
    _ = (endpointCutFirstLabels H y).card * ((r - 1) * Δ) := by simp
    _ ≤ ((r - 1) * vertexDegree H y) * ((r - 1) * Δ) :=
      Nat.mul_le_mul_right _ (endpointCutFirstLabels_card_le hH y)
    _ = _ := by ring

theorem endpointCutLabels_card_le {r Δ : ℕ} {H : SimpleHypergraph V}
    (hH : H ⊆ completeEdges V r) (hΔ : ∀ v, vertexDegree H v ≤ Δ)
    (y : V) (mate : V → V) :
    (endpointCutFirstLabels H y).card + (endpointCutSecondLabels H y mate).card ≤
      (r - 1) * vertexDegree H y + (r - 1)^2 * vertexDegree H y * Δ :=
  Nat.add_le_add (endpointCutFirstLabels_card_le hH y)
    (endpointCutSecondLabels_card_le hH hΔ y mate)

/-- Simplicity and uniformity bound every degree polynomially in the vertex count. -/
theorem vertexDegree_le_card_pow {r : ℕ} {H : SimpleHypergraph V}
    (hH : H ⊆ completeEdges V r) (y : V) :
    vertexDegree H y ≤ (Fintype.card V) ^ (r - 1) := by
  have hcard : vertexDegree H y ≤ ((univ : Finset V).powersetCard (r - 1)).card := by
    apply card_le_card_of_injOn (fun e => e.erase y)
    · intro e he
      have hm := mem_filter.mp he
      apply mem_powersetCard.mpr
      exact ⟨subset_univ _, by rw [card_erase_of_mem hm.2,
        (mem_completeEdges r e).mp (hH hm.1)]⟩
    · intro e he f hf hef
      have hy := (mem_filter.mp he).2
      have hy' := (mem_filter.mp hf).2
      calc
        e = insert y (e.erase y) := (insert_erase hy).symm
        _ = insert y (f.erase y) := congrArg (insert y) hef
        _ = f := insert_erase hy'
  exact hcard.trans (by rw [card_powersetCard, card_univ]; exact Nat.choose_le_pow _ _)

/-- Explicit constant in the polynomial endpoint-label estimate. -/
@[expose] def endpointCutConstant (r : ℕ) : ℕ := (r - 1) + (r - 1)^2

theorem endpointCutLabels_card_le_polynomial {r : ℕ} {H : SimpleHypergraph V}
    (hr : 1 ≤ r) (hH : H ⊆ completeEdges V r) (y : V) (mate : V → V) :
    (endpointCutFirstLabels H y).card + (endpointCutSecondLabels H y mate).card ≤
      endpointCutConstant r * (Fintype.card V) ^ (2 * r - 2) := by
  let N := Fintype.card V
  have hN : 1 ≤ N := Fintype.card_pos_iff.mpr ⟨y⟩
  have hpow : 1 ≤ N ^ (r - 1) := one_le_pow₀ hN
  have hdeg : ∀ v, vertexDegree H v ≤ N ^ (r - 1) := vertexDegree_le_card_pow hH
  have hexp : 2 * r - 2 = (r - 1) + (r - 1) := by omega
  calc
    _ ≤ (r - 1) * vertexDegree H y +
        (r - 1)^2 * vertexDegree H y * N ^ (r - 1) :=
      endpointCutLabels_card_le hH hdeg y mate
    _ ≤ (r - 1) * N ^ (r - 1) + (r - 1)^2 * N ^ (r - 1) * N ^ (r - 1) := by
      exact Nat.add_le_add (Nat.mul_le_mul_left _ (hdeg y))
        (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (hdeg y)))
    _ ≤ (r - 1) * (N ^ (r - 1) * N ^ (r - 1)) +
        (r - 1)^2 * N ^ (r - 1) * N ^ (r - 1) := by
      apply Nat.add_le_add_right
      exact Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_right _ hpow)
    _ = _ := by rw [hexp, pow_add]; unfold endpointCutConstant N; ring

end LooseHamilton
