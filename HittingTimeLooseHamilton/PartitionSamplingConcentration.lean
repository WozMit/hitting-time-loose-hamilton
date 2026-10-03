module

public import HittingTimeLooseHamilton.HypergeometricFamilyConcentration
public import HittingTimeLooseHamilton.PathRegularityModels

public section

/-! Concentration over every vertex partition and every process time. -/
noncomputable section
namespace LooseHamilton
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

@[expose] def partitionTest (r : ℕ) (A : Finset V) : SimpleHypergraph V :=
  (completeEdges V r).filter (fun e => (e ∩ A).card=2)

lemma partitionTest_subset (r : ℕ) (A : Finset V) : partitionTest r A ⊆ completeEdges V r :=
  filter_subset _ _

lemma partitionCount_eq_inter (r : ℕ) (F : SimpleHypergraph V)
    (hF : F ⊆ completeEdges V r) (A : Finset V) :
    partitionCount F A = (F ∩ partitionTest r A).card := by
  unfold partitionCount
  congr 1
  ext e
  simp only [mem_filter,mem_inter,partitionTest]
  constructor
  · rintro ⟨he,ha⟩
    exact ⟨he,hF he,ha⟩
  · tauto

/-- The sampling error is centred at the exact complete-host density, before
approximating it by the paper's constant theta_r. -/
@[expose] def PartitionSamplingFailure (r M : ℕ) (δ : ℝ) (F : ℕ → SimpleHypergraph V) : Prop :=
  ∃ A : Finset V, ∃ j : ℕ, M≤j ∧ j≤(completeEdges V r).card ∧
    δ*j ≤ |(partitionCount (F j) A:ℝ)-(j:ℝ)/(completeEdges V r).card*(partitionTest r A).card|

lemma process_partition_sampling_probability (r M : ℕ) (hM : 0<M) (δ : ℝ) (hδ : 0<δ) :
    (processLaw V r).event (fun σ => PartitionSamplingFailure r M δ (processState σ)) ≤
      (2:ℝ)^(Fintype.card V)*((completeEdges V r).card+1)*2*Real.exp (-δ^2*M/4) := by
  have h := process_test_family_concentration (partitionTest (V:=V) r)
    (partitionTest_subset r) M hM δ hδ
  have he (σ : EdgeOrder V r) : PartitionSamplingFailure r M δ (processState σ) ↔
      ∃ A : Finset V, ∃ j : ℕ, M≤j ∧ j≤(completeEdges V r).card ∧
        δ*j ≤ |((processState σ j ∩ partitionTest r A).card:ℝ)-
          (j:ℝ)/(completeEdges V r).card*(partitionTest r A).card| := by
    unfold PartitionSamplingFailure
    simp_rw [partitionCount_eq_inter r _ (processState_subset σ _)]
  simp_rw [he]
  simpa only [Fintype.card_finset,Nat.cast_pow,Nat.cast_ofNat] using h
end LooseHamilton
