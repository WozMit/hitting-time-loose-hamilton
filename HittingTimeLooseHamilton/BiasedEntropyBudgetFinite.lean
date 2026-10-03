module

public import HittingTimeLooseHamilton.BiasedEntropyBudgetSupport
public import HittingTimeLooseHamilton.BiasedEntropyMean
public import HittingTimeLooseHamilton.BiasedEntropyCloneAverage
public import HittingTimeLooseHamilton.BiasedMatchingDeficitBudget

public section

open scoped BigOperators
noncomputable section
namespace LooseHamilton.BiasedRoleInstance
open FiniteEntropy
variable {r : ℕ}

@[expose] def meanLocalDeficit (D : BiasedRoleInstance r) (hr : 3≤r) : ℝ :=
  BiasedEnsemble.meanLocalDeficit hr D.uniformCard D.root D.initial D.cycleLaw

@[expose] def meanDegreeDeficit (D : BiasedRoleInstance r) (hr : 3≤r) : ℝ :=
  BiasedEnsemble.meanDegreeDeficit hr D.uniformCard D.root D.initial D.cycleLaw

@[expose] def meanCollision (D : BiasedRoleInstance r) (hr : 3≤r) : ℝ :=
  ∑ i, D.ensembleLaw.mass i*Kahn.MatchingLaw.errorSum (D.ensembleMatchingLaw hr i)

@[expose] def entropyDeficit (D : BiasedRoleInstance r) (hr : 3≤r) : ℝ :=
  D.roleDeficit+D.meanLocalDeficit hr+D.meanDegreeDeficit hr

/-- The conditional Kahn bounds supplied by the already proved Theorem 4.2. -/
@[expose] def KahnBounds (D : BiasedRoleInstance r) (hr : 3≤r) (C₁ C₂ : ℝ) : Prop :=
  ∀ i, entropy (D.ensembleMatchingLaw hr i).mass <
    (1/(r:ℝ))*Kahn.MatchingLaw.marginalEntropySum (D.ensembleMatchingLaw hr i)-
      Kahn.correction (r*D.k) r+C₁*Kahn.MatchingLaw.errorSum (D.ensembleMatchingLaw hr i)+
      C₂*Real.log (r*D.k:ℕ)

lemma meanLocalDeficit_nonneg (D : BiasedRoleInstance r) (hr : 3≤r) :
    0≤D.meanLocalDeficit hr := BiasedEnsemble.meanLocalDeficit_nonneg _ _ _ _ _
lemma meanDegreeDeficit_nonneg (D : BiasedRoleInstance r) (hr : 3≤r) :
    0≤D.meanDegreeDeficit hr := BiasedEnsemble.meanDegreeDeficit_nonneg _ _ _ _ _ (D.k_pos hr)

lemma ensemble_mean_log_upper (D : BiasedRoleInstance r) (hr : 3≤r)
    (C δ : ℝ) (hC : 0≤C) (hμ : 1≤D.μ)
    (hdeg : ∀v,(vertexDegree D.host v:ℝ)≤C*D.μ)
    (hs : 2*D.s≤D.N) (hpart : D.partitionBound δ) :
    (∑ i, D.ensembleLaw.mass i*Real.log (kahnMeanDegree (D.ensembleHost hr i))) ≤
      Real.log D.cloneLambda0+cloneRelativeConstant r C*(δ+(D.s:ℝ)/D.N) := by
  have hδ := D.partitionBound_nonneg hr hpart
  have h := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset D.ensembleIndex)) =>
    mul_le_mul_of_nonneg_left
      (D.clone_mean_log_upper hr D.uniformCard C δ hC hδ hμ hdeg hs hpart i)
      (D.ensembleLaw.nonneg i))
  simp only [← Finset.sum_mul,D.ensembleLaw.total,one_mul] at h
  exact h

lemma actual_three_deficits (D : BiasedRoleInstance r) (hr : 3≤r)
    {ξ C₁ C₂ : ℝ} (hK : D.KahnBounds hr C₁ C₂) (hent : D.entropyBound ξ) :
    D.roleDeficit+(D.meanLocalDeficit hr+D.meanDegreeDeficit hr)/(r:ℝ) ≤
      D.roleSupport+(D.k:ℝ)*(∑ i, D.ensembleLaw.mass i*
        Real.log (kahnMeanDegree (D.ensembleHost hr i)))-
      (D.k:ℝ)*Real.log (((r:ℝ)-1)*D.μ)+ξ*D.N+
      C₁*D.meanCollision hr+C₂*Real.log (r*D.k:ℕ) := by
  have h := kahn_three_deficits_budget D.ensembleLaw (D.ensembleHost hr) (D.ensembleMatchingLaw hr)
    (by omega) rfl (fun i => kahnLocalDeficit (D.ensembleMatchingLaw hr i))
    (fun i => kahnDegreeDeficit (D.ensembleHost hr i) (kahnMeanDegree (D.ensembleHost hr i)))
    (fun i => kahnMeanDegree (D.ensembleHost hr i))
    (entropy D.cycleLaw.mass) D.roleEntropy D.roleSupport D.μ (ξ*D.N) C₁ C₂
    (D.ensemble_entropy_chain hr) (by
      intro i
      have hi := kahn_deficits_add (D.ensembleMatchingLaw hr i) (kahnMeanDegree (D.ensembleHost hr i))
      linarith) hK hent
  have heq : (∑ i, D.ensembleLaw.mass i*
      (kahnLocalDeficit (D.ensembleMatchingLaw hr i)+
        kahnDegreeDeficit (D.ensembleHost hr i) (kahnMeanDegree (D.ensembleHost hr i)))) =
      D.meanLocalDeficit hr+D.meanDegreeDeficit hr := by
    simp_rw [mul_add,Finset.sum_add_distrib]
    rfl
  rw [heq] at h
  exact h

/-- Quantitative finite three-deficit estimate, with genuine conditional laws.
The remaining probabilistic correction is exactly the mean Kahn collision sum. -/
lemma actual_entropy_deficit_bound (r : ℕ) (hr : 3≤r) :
    ∃ A : ℝ, 0≤A ∧ ∀ (D : BiasedRoleInstance r) (C δ ξ C₁ C₂ : ℝ),
      0≤C → 1≤D.μ → D.s<D.k → 3*D.s≤D.N →
      (∀v,(vertexDegree D.host v:ℝ)≤C*D.μ) → D.partitionBound δ →
      D.entropyBound ξ → D.KahnBounds hr C₁ C₂ →
      D.entropyDeficit hr ≤ (r:ℝ)*
        (A*((D.s:ℝ)+Real.log ((D.N:ℝ)+1)+1)+
          (D.k:ℝ)*cloneRelativeConstant r C*(δ+(D.s:ℝ)/D.N)+ξ*D.N+
          C₁*D.meanCollision hr+C₂*Real.log (r*D.k:ℕ)) := by
  obtain ⟨A,hA,hcancel⟩ := roleSupport_density_cancellation r hr
  refine ⟨A,hA,?_⟩
  intro D C δ ξ C₁ C₂ hC hμ hsk hsN hdeg hpart hent hK
  have h := D.actual_three_deficits hr hK hent
  have hlog := D.ensemble_mean_log_upper hr C δ hC hμ hdeg (by omega) hpart
  have hsupp := (abs_le.mp (hcancel D hsk hsN)).2
  change D.roleSupport+(D.k:ℝ)*Real.log D.cloneLambda0-
    (D.k:ℝ)*Real.log (((r:ℝ)-1)*D.μ)≤_ at hsupp
  have hmul := mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg D.k : (0:ℝ)≤D.k)
  have hbound : D.roleDeficit+(D.meanLocalDeficit hr+D.meanDegreeDeficit hr)/(r:ℝ) ≤
      A*((D.s:ℝ)+Real.log ((D.N:ℝ)+1)+1)+
        (D.k:ℝ)*cloneRelativeConstant r C*(δ+(D.s:ℝ)/D.N)+ξ*D.N+
          C₁*D.meanCollision hr+C₂*Real.log (r*D.k:ℕ) := by linarith
  have hrR : (1:ℝ)≤r := by exact_mod_cast (show 1≤r by omega)
  have hsum := FiniteEntropy.three_deficit_absorption (by linarith : (0:ℝ)<r)
    (D.roleDeficit_nonneg hr)
    (add_nonneg (D.meanLocalDeficit_nonneg hr) (D.meanDegreeDeficit_nonneg hr)) hbound
  rw [max_eq_right hrR] at hsum
  simpa only [entropyDeficit,add_assoc] using hsum

end LooseHamilton.BiasedRoleInstance
