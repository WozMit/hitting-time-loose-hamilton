module

public import HittingTimeLooseHamilton.BiasedRoleFiniteConclusion

public section

open scoped BigOperators
noncomputable section
namespace LooseHamilton.BiasedRoleInstance
open FiniteEntropy Finset
variable {r : ℕ}

/-- Average the genuine per-role change of clone reference degree. -/
lemma meanRelativeError_le (D : BiasedRoleInstance r) (hr : 3≤r)
    (C δ : ℝ) (hC : 0≤C) (hμ : 1≤D.μ)
    (hdeg : ∀v,(vertexDegree D.host v:ℝ)≤C*D.μ)
    (hs : 2*D.s≤D.N) (hpart : D.partitionBound δ) :
    D.meanRelativeError hr≤cloneRelativeConstant r C*(δ+(D.s:ℝ)/D.N) := by
  have hh := sum_le_sum (fun i (_ : i∈(univ : Finset D.ensembleIndex)) =>
    mul_le_mul_of_nonneg_left
      (D.clone_mean_relative hr D.uniformCard C δ hC (D.partitionBound_nonneg hr hpart)
        hμ hdeg hs hpart i) (D.ensembleLaw.nonneg i))
  simp only [← sum_mul,D.ensembleLaw.total,one_mul] at hh
  exact hh

end LooseHamilton.BiasedRoleInstance
