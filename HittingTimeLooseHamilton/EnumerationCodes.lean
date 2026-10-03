module

public import HittingTimeLooseHamilton.JunctionChoices
public import HittingTimeLooseHamilton.Allocation
public import HittingTimeLooseHamilton.BlockEnumeration
public import HittingTimeLooseHamilton.EnumerationStatement
public import HittingTimeLooseHamilton.ProhibitionBound

public section

/-! # Cardinalities of complete-host enumeration data

These theorems count the proposed data, not the existing cycle edge sets.
The separate decoder/reconstruction equivalence is indispensable for Proposition 2.2.
-/
noncomputable section
open scoped BigOperators
namespace LooseHamilton
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The vertices remaining after selecting junctions and marked ports. -/
abbrev PrivatePool (markers : Finset (Finset V)) (J : Finset V) :=
  ↥(Finset.univ \ (originalPorts markers ∪ J))

/-- Rooted directed block data with unordered private blocks. The root marker's
orientation is fixed externally; it is not an extra choice in this type. -/
@[expose] def CompleteHostCode (r k : ℕ) (markers : Finset (Finset V)) (root : Finset V) :=
  Σ J : ↥(ordinaryJunctionChoices markers k),
    MarkerDirections markers root × BlockEnumeration.RootedOrder k ×
      Allocation.Blocks (PrivatePool markers J.val) k (r - 2)

@[expose] instance {r k : ℕ} {markers : Finset (Finset V)} {root : Finset V} :
    Fintype (CompleteHostCode r k markers root) := by
  unfold CompleteHostCode
  infer_instance

/-- The same data, with a separated marked-block order. -/
@[expose] def AllowedHostCode (r k : ℕ) (markers : Finset (Finset V)) (root : Finset V) :=
  Σ J : ↥(ordinaryJunctionChoices markers k),
    MarkerDirections markers root × BlockEnumeration.SeparatedOrder k markers.card ×
      Allocation.Blocks (PrivatePool markers J.val) k (r - 2)

@[expose] instance {r k : ℕ} {markers : Finset (Finset V)} {root : Finset V} :
    Fintype (AllowedHostCode r k markers root) := by
  unfold AllowedHostCode
  infer_instance

theorem privatePool_fintype_card {markers : Finset (Finset V)}
    (hM : IsPairMatching markers) {r k : ℕ} (hr : 3 ≤ r) (hsk : markers.card ≤ k)
    (hN : Fintype.card V = (r - 1) * k + markers.card)
    (J : ↥(ordinaryJunctionChoices markers k)) :
    Fintype.card (PrivatePool markers J.val) = k * (r - 2) := by
  rw [Fintype.card_coe, privatePool_card hM hr hsk hN J.property, Nat.mul_comm]

/-- Exact cardinality of the unrestricted data type. -/
theorem completeHostCode_card {r k : ℕ} {markers : Finset (Finset V)}
    {root : Finset V} (hr : 3 ≤ r) (hM : IsPairMatching markers)
    (hroot : root ∈ markers) (hsk : markers.card ≤ k)
    (hN : Fintype.card V = (r - 1) * k + markers.card) :
    Fintype.card (CompleteHostCode r k markers root) =
      completeHostFormula r (Fintype.card V) k markers.card := by
  unfold CompleteHostCode
  rw [Fintype.card_sigma]
  simp only [Fintype.card_prod, markerDirections_card hM hroot,
    BlockEnumeration.card_rootedOrder]
  have ha (J : ↥(ordinaryJunctionChoices markers k)) :
      Fintype.card (Allocation.Blocks (PrivatePool markers J.val) k (r - 2)) =
        (k * (r - 2)).factorial / (r - 2).factorial ^ k :=
    Allocation.blocks_card_eq _ _ _ (privatePool_fintype_card hM hr hsk hN J)
  simp_rw [ha]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_coe,
    ordinaryJunctionChoices_card hM]
  simp only [nsmul_eq_mul, Nat.cast_id, completeHostFormula]
  rw [Nat.mul_comm k (r - 2)]
  ring

/-- Exact cardinality of the separated-order data type. -/
theorem allowedHostCode_card {r k : ℕ} {markers : Finset (Finset V)}
    {root : Finset V} (hr : 3 ≤ r) (hM : IsPairMatching markers)
    (hroot : root ∈ markers) (hsk : markers.card ≤ k)
    (hN : Fintype.card V = (r - 1) * k + markers.card) :
    Fintype.card (AllowedHostCode r k markers root) =
      (Fintype.card V - 2 * markers.card).choose (k - markers.card) *
      (2 ^ (markers.card - 1) *
        (Fintype.card (BlockEnumeration.SeparatedOrder k markers.card) *
          ((k * (r - 2)).factorial / (r - 2).factorial ^ k))) := by
  unfold AllowedHostCode
  rw [Fintype.card_sigma]
  simp only [Fintype.card_prod, markerDirections_card hM hroot]
  have ha (J : ↥(ordinaryJunctionChoices markers k)) :
      Fintype.card (Allocation.Blocks (PrivatePool markers J.val) k (r - 2)) =
        (k * (r - 2)).factorial / (r - 2).factorial ^ k :=
    Allocation.blocks_card_eq _ _ _ (privatePool_fintype_card hM hr hsk hN J)
  simp_rw [ha]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_coe,
    ordinaryJunctionChoices_card hM]
  rfl

/-- The ratio of the separated and unrestricted data counts. This is still a
statement about data; it becomes a statement about cycle counts only after
both decoder equivalences are established. -/
theorem allowedHostCode_card_ratio {r k : ℕ} {markers : Finset (Finset V)}
    {root : Finset V} (hr : 3 ≤ r) (hM : IsPairMatching markers)
    (hroot : root ∈ markers) (hks : 2 * markers.card ≤ k)
    (hN : Fintype.card V = (r - 1) * k + markers.card) :
    (Fintype.card (AllowedHostCode r k markers root) : ℝ) =
      (Fintype.card (CompleteHostCode r k markers root) : ℝ) *
        prohibitionRatio k markers.card := by
  have hsk : markers.card ≤ k := by omega
  rw [allowedHostCode_card hr hM hroot hsk hN,
    completeHostCode_card hr hM hroot hsk hN]
  have hc := congrArg (fun n : ℕ => (n : ℝ))
    (BlockEnumeration.card_separatedOrder_mul_factorial hks)
  push_cast at hc ⊢
  unfold completeHostFormula prohibitionRatio
  push_cast
  have h₁ : ((k - 1).factorial : ℝ) ≠ 0 := by positivity
  have h₂ : ((k - 2 * markers.card).factorial : ℝ) ≠ 0 := by positivity
  have he : (Fintype.card (BlockEnumeration.SeparatedOrder k markers.card) : ℝ) =
      ((k - markers.card).factorial : ℝ) * (k - markers.card - 1).factorial /
        (k - 2 * markers.card).factorial := (eq_div_iff h₂).mpr hc
  rw [he, Nat.mul_comm k (r - 2)]
  field_simp
  <;> ring

end LooseHamilton
