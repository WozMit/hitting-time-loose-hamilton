module

public import HittingTimeLooseHamilton.BiasedEntropyMean
public import HittingTimeLooseHamilton.BiasedEntropyBudgetModels

public section

noncomputable section
namespace LooseHamilton.BiasedRoleInstance
open Finset FiniteEntropy
open scoped BigOperators
variable {r : ℕ}

lemma clone_mean_relative_average (D : BiasedRoleInstance r) (hr : 3≤r)
    (C δ : ℝ) (hC : 0≤C) (hδ : 0≤δ)
    (hμ : 1≤D.μ) (hdeg : ∀v, (vertexDegree D.host v:ℝ)≤C*D.μ)
    (hs : 2*D.s≤D.N) (hpart : D.partitionBound δ) :
    (∑ z, D.ensembleLaw.mass z * |kahnMeanDegree (D.ensembleHost hr z)/D.cloneLambda0-1|) ≤
      cloneRelativeConstant r C*(δ+(D.s:ℝ)/D.N) := by
  have hs' := sum_le_sum (s := univ) (fun z _ => mul_le_mul_of_nonneg_left
    (D.clone_mean_relative hr D.uniformCard C δ hC hδ hμ hdeg hs hpart z)
    (D.ensembleLaw.nonneg z))
  simp only [← sum_mul, D.ensembleLaw.total, one_mul] at hs'
  exact hs'

lemma clone_mean_log_average (D : BiasedRoleInstance r) (hr : 3≤r)
    (C δ : ℝ) (hC : 0≤C) (hδ : 0≤δ)
    (hμ : 1≤D.μ) (hdeg : ∀v, (vertexDegree D.host v:ℝ)≤C*D.μ)
    (hs : 2*D.s≤D.N) (hpart : D.partitionBound δ) :
    (∑ z, D.ensembleLaw.mass z * Real.log (kahnMeanDegree (D.ensembleHost hr z))) ≤
      Real.log D.cloneLambda0+cloneRelativeConstant r C*(δ+(D.s:ℝ)/D.N) := by
  have hs' := sum_le_sum (s := univ) (fun z _ => mul_le_mul_of_nonneg_left
    (D.clone_mean_log_upper hr D.uniformCard C δ hC hδ hμ hdeg hs hpart z)
    (D.ensembleLaw.nonneg z))
  simp only [← sum_mul, D.ensembleLaw.total, one_mul] at hs'
  exact hs'

lemma clone_mean_comparable (D : BiasedRoleInstance r) (hr : 3≤r)
    (C δ : ℝ) (hC : 0≤C) (hδ : 0≤δ)
    (hμ : 1≤D.μ) (hdeg : ∀v, (vertexDegree D.host v:ℝ)≤C*D.μ)
    (hs : 2*D.s≤D.N) (hpart : D.partitionBound δ)
    (hsmall : cloneRelativeConstant r C*(δ+(D.s:ℝ)/D.N)≤1/2)
    (z : D.ensembleIndex) :
    D.cloneLambda0/2 ≤ kahnMeanDegree (D.ensembleHost hr z) ∧
      kahnMeanDegree (D.ensembleHost hr z) ≤ 2*D.cloneLambda0 := by
  have hb := D.clone_mean_relative hr D.uniformCard C δ hC hδ hμ hdeg hs hpart z
  change |kahnMeanDegree (D.ensembleHost hr z)/D.cloneLambda0-1|≤_ at hb
  have hb' := abs_le.mp (hb.trans hsmall)
  have hbase := D.cloneLambda0_pos hr
  have hlo : (1/2:ℝ)≤kahnMeanDegree (D.ensembleHost hr z)/D.cloneLambda0 := by linarith
  have hup : kahnMeanDegree (D.ensembleHost hr z)/D.cloneLambda0≤2 := by linarith
  have hlo' := (le_div_iff₀ hbase).mp hlo
  have hup' := (div_le_iff₀ hbase).mp hup
  exact ⟨by linarith, hup'⟩
end LooseHamilton.BiasedRoleInstance
