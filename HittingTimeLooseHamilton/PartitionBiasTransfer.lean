module

public import HittingTimeLooseHamilton.PartitionHostCount
public import HittingTimeLooseHamilton.PartitionSamplingConcentration
public import HittingTimeLooseHamilton.PartitionRatioScales

public section

/-! Transfer from concentration at the exact finite density to theta_r. -/
noncomputable section
namespace LooseHamilton
open Finset Filter
variable {V : Type*} [Fintype V] [DecidableEq V]

lemma partition_test_ratio (r : ℕ) (hr : 2 ≤ r) (A : Finset V) (m : ℕ) :
    (m:ℝ)/(completeEdges V r).card*(partitionTest r A).card =
      (m:ℝ)*completePartitionRatio r (Fintype.card V) A.card := by
  have hc : (partitionTest r A).card =
      A.card.choose 2*(Fintype.card V-A.card).choose (r-2) := complete_partition_count r hr A
  rw [hc,completeEdges_card,Nat.cast_mul]
  unfold completePartitionRatio
  ring

/-- The exact finite bias plus a sampling error yields the displayed partition estimate. -/
theorem path_partition_of_sampling (r : ℕ) (hr : 3 ≤ r) (L : ℝ)
    (F : SimpleHypergraph V) (hn : 0 < Fintype.card V)
    (hbias : ∀ A : Finset V, |(A.card:ℝ)-junctionFraction r*Fintype.card V| ≤
      L*(Fintype.card V:ℝ)^(1/10:ℝ) →
      |completePartitionRatio r (Fintype.card V) A.card-partitionDensity r| ≤
        (Real.log (Fintype.card V:ℝ))^(-1/8:ℝ))
    (hsample : ∀ A : Finset V,
      |(partitionCount F A:ℝ)-(F.card:ℝ)/(completeEdges V r).card*(partitionTest r A).card| ≤
        (Real.log (Fintype.card V:ℝ))^(-1/8:ℝ)*F.card) :
    PathPartitionRegular r 2 L F := by
  intro A hA
  let δ := (Real.log (Fintype.card V:ℝ))^(-1/8:ℝ)
  have hd : 0 ≤ δ := Real.rpow_nonneg
    (Real.log_nonneg (by exact_mod_cast hn)) _
  have hs := hsample A
  rw [partition_test_ratio r (by omega)] at hs
  have hb := hbias A hA
  have he : |(partitionCount F A:ℝ)-partitionDensity r*F.card| ≤ 2*(F.card:ℝ)*δ := by
    calc
      _ = |((partitionCount F A:ℝ)-F.card*completePartitionRatio r (Fintype.card V) A.card) +
          F.card*(completePartitionRatio r (Fintype.card V) A.card-partitionDensity r)| := by
        congr 1; ring
      _ ≤ |(partitionCount F A:ℝ)-F.card*completePartitionRatio r (Fintype.card V) A.card| +
          |F.card*(completePartitionRatio r (Fintype.card V) A.card-partitionDensity r)| := abs_add_le _ _
      _ ≤ δ*F.card+(F.card:ℝ)*δ := by
        rw [abs_mul]
        rw [show |(F.card:ℝ)| = (F.card:ℝ) from abs_of_nonneg (Nat.cast_nonneg _)]
        exact add_le_add hs (mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg _))
      _ = _ := by ring
  have hn0 : (Fintype.card V:ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
  have hmean : (Fintype.card V:ℝ)*meanDegree (V:=V) r F.card = (r:ℝ)*F.card := by
    unfold meanDegree
    field_simp
  calc
    _ ≤ 2*(F.card:ℝ)*δ := he
    _ ≤ 2*((r:ℝ)*F.card)*δ := by
      have hr1 : (1:ℝ) ≤ r := by exact_mod_cast (show 1≤r by omega)
      gcongr
      nlinarith [Nat.cast_nonneg (α:=ℝ) F.card]
    _ = _ := by rw [←hmean]; dsimp [δ]; ring

/-- On the complement of the single sampling failure event, every time and every
admissible partition meets the paper's deterministic theta_r bound. -/
theorem path_partitions_of_no_sampling_failure (r : ℕ) (hr : 3 ≤ r)
    (M : ℕ) (ell : V → ℕ) (L : ℝ) (hn : 0 < Fintype.card V)
    (hbias : ∀ k : ℕ, k ≤ Fintype.card V →
      |(k:ℝ)-junctionFraction r*Fintype.card V| ≤ L*(Fintype.card V:ℝ)^(1/10:ℝ) →
      |completePartitionRatio r (Fintype.card V) k-partitionDensity r| ≤
        (Real.log (Fintype.card V:ℝ))^(-1/8:ℝ))
    (ω : TerminalState V r M ell × MissingOrder V r M)
    (hgood : ¬PartitionSamplingFailure r M ((Real.log (Fintype.card V:ℝ))^(-1/8:ℝ))
      (extensionState ω.1 ω.2)) :
    ∀ j, M ≤ j → j ≤ (completeEdges V r).card →
      PathPartitionRegular r 2 L (extensionState ω.1 ω.2 j) := by
  intro j hMj hjK
  apply path_partition_of_sampling r hr L _ hn
  · intro A hA
    exact hbias A.card (card_le_univ _) hA
  · intro A
    rw [extensionState_card _ _ _ hMj hjK]
    exact (lt_of_not_ge (fun h => hgood ⟨A,j,hMj,hjK,h⟩)).le
end LooseHamilton
