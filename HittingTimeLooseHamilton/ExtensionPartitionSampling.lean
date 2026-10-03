module

public import HittingTimeLooseHamilton.PartitionSamplingConcentration
public import HittingTimeLooseHamilton.ExtensionFamilyConcentration

public section

/-! Exact centred partition sampling errors under Q, with terminal conditioning accounted for. -/
noncomputable section
namespace LooseHamilton
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

lemma extension_partition_sampling_probability (r M : ℕ) (ell : V → ℕ)
    [Nonempty (TerminalState V r M ell)] (hM : 0<M) (δ : ℝ) (hδ : 0<δ)
    (hb : 0<terminalFeasibilityProbability r M ell) :
    (extensionLaw r M ell).event (fun ω =>
      PartitionSamplingFailure r M δ (extensionState ω.1 ω.2)) ≤
      (2:ℝ)^(Fintype.card V)*((completeEdges V r).card+1)*2*Real.exp (-δ^2*M/4) /
        terminalFeasibilityProbability r M ell := by
  have h := extension_test_family_concentration (partitionTest (V:=V) r)
    (partitionTest_subset r) M ell hM δ hδ hb
  have he (ω : TerminalState V r M ell × MissingOrder V r M) :
      PartitionSamplingFailure r M δ (extensionState ω.1 ω.2) ↔
      ∃ A : Finset V, ∃ j : ℕ, M≤j ∧ j≤(completeEdges V r).card ∧
        δ*j ≤ |((extensionState ω.1 ω.2 j ∩ partitionTest r A).card:ℝ)-
          (j:ℝ)/(completeEdges V r).card*(partitionTest r A).card| := by
    unfold PartitionSamplingFailure
    simp_rw [partitionCount_eq_inter r _ (extensionState_subset ω.1 ω.2 _)]
  simp_rw [he]
  simpa only [Fintype.card_finset,Nat.cast_pow,Nat.cast_ofNat] using h

lemma extension_partition_sampling_beta_bound (r M : ℕ) (ell : V → ℕ)
    [Nonempty (TerminalState V r M ell)] (hM : 0<M) (δ : ℝ) (hδ : 0<δ)
    (hb : Real.exp (-(Fintype.card V:ℝ)^(1/10:ℝ)) ≤ terminalFeasibilityProbability r M ell) :
    (extensionLaw r M ell).event (fun ω =>
      PartitionSamplingFailure r M δ (extensionState ω.1 ω.2)) ≤
      (2:ℝ)^(Fintype.card V)*((completeEdges V r).card+1)*2*Real.exp (-δ^2*M/4) *
        Real.exp ((Fintype.card V:ℝ)^(1/10:ℝ)) := by
  have hb0 : 0<terminalFeasibilityProbability r M ell := (Real.exp_pos _).trans_le hb
  apply (extension_partition_sampling_probability r M ell hM δ hδ hb0).trans
  calc
    _ ≤ _ / Real.exp (-(Fintype.card V:ℝ)^(1/10:ℝ)) :=
      div_le_div_of_nonneg_left (by positivity) (Real.exp_pos _) hb
    _ = _ := by rw [Real.exp_neg,div_inv_eq_mul]
end LooseHamilton
