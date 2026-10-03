module

public import HittingTimeLooseHamilton.PathPortRegularity

public section

/-! Deterministic preservation of upper regularity under a small deletion batch.
The hypotheses concern only the mean and the number of deleted edges. -/
noncomputable section
namespace LooseHamilton
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem candidate_batch_upper_regular {r : ℕ} {C L : ℝ}
    {J F : SimpleHypergraph V} (hC : 0 ≤ C) (hr : 2 ≤ r)
    (hJ : PathGraphUpperRegular r C L J) (hF : F ⊆ J)
    (hmean : meanDegree (V := V) r J.card ≤ 2 * meanDegree (V := V) r F.card)
    (hloss : (1 + partitionDensity r) * ((J.card : ℝ) - F.card) ≤
      C * Fintype.card V * meanDegree (V := V) r J.card *
        (Real.log (Fintype.card V : ℝ)) ^ (-1/8 : ℝ)) :
    PathGraphUpperRegular r (4*C) L F := by
  let μ := meanDegree (V := V) r J.card
  let ν := meanDegree (V := V) r F.card
  have hν : 0 ≤ ν := by unfold ν meanDegree; positivity
  have hcmean : C * μ ≤ 4*C*ν := by
    have hm := mul_le_mul_of_nonneg_left hmean hC
    change C * μ ≤ C * (2*ν) at hm
    nlinarith
  constructor
  · intro v
    exact (Nat.cast_le.mpr (vertexDegree_mono hF v)).trans
      ((hJ.upper_degree v).trans hcmean)
  · intro v w hvw
    exact (Nat.cast_le.mpr (pairDegree_mono hF v w)).trans
      ((hJ.codegree v w hvw).trans (mul_le_mul_of_nonneg_right hcmean
        (Real.rpow_nonneg (Real.log_natCast_nonneg _) _)))
  · intro A hA
    have ht := filter_discrepancy_transfer hF (fun e => (e∩A).card=2)
      (partitionDensity r)
      (C*Fintype.card V*μ*(Real.log (Fintype.card V:ℝ))^(-1/8:ℝ))
      (partitionDensity_nonneg hr) (hJ.partitions A hA)
    change |(partitionCount F A:ℝ)-partitionDensity r*F.card| ≤
      C*Fintype.card V*μ*(Real.log (Fintype.card V:ℝ))^(-1/8:ℝ)+
      (1+partitionDensity r)*((J.card-F.card:ℕ):ℝ) at ht
    rw [Nat.cast_sub (card_le_card hF)] at ht
    have hf : 0 ≤ (Real.log (Fintype.card V:ℝ))^(-1/8:ℝ) :=
      Real.rpow_nonneg (Real.log_natCast_nonneg _) _
    have hm := mul_le_mul_of_nonneg_right hmean
      (mul_nonneg (mul_nonneg hC (Nat.cast_nonneg (Fintype.card V))) hf)
    change |(partitionCount F A:ℝ)-partitionDensity r*F.card| ≤ _
    dsimp [μ,ν] at *
    nlinarith

end LooseHamilton
