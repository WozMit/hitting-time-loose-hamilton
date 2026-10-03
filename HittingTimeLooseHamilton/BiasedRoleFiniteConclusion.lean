module

public import HittingTimeLooseHamilton.BiasedEntropyBudgetFinite
public import HittingTimeLooseHamilton.BiasedEntropyJunctionBudget
public import HittingTimeLooseHamilton.BiasedRoleReference
public import HittingTimeLooseHamilton.BiasedRoleCloneBias
public import HittingTimeLooseHamilton.BiasedEntropyFinalBound

public section

open scoped BigOperators
noncomputable section
namespace LooseHamilton.BiasedRoleInstance
open FiniteEntropy Finset
variable {r : ℕ}

/-- Actual average change from the conditional clone mean to the common reference. -/
@[expose] def meanRelativeError (D : BiasedRoleInstance r) (hr : 3≤r) : ℝ :=
  ∑ i, D.ensembleLaw.mass i * |kahnMeanDegree (D.ensembleHost hr i)/D.cloneLambda0-1|

lemma meanRelativeError_nonneg (D : BiasedRoleInstance r) (hr : 3≤r) :
    0≤D.meanRelativeError hr :=
  sum_nonneg (fun i _ => mul_nonneg (D.ensembleLaw.nonneg i) (abs_nonneg _))

lemma role_clone_deviation_bound (D : BiasedRoleInstance r) (hr : 3≤r) :
    roleCloneDeviation r D.markers D.host D.root D.initial D.cycleLaw D.cloneLambda0 ≤
      (2/(r:ℝ))*Real.sqrt (2*(r*D.k:ℕ)*
        (D.meanLocalDeficit hr+D.meanDegreeDeficit hr))+
      ((r*D.k:ℕ):ℝ)/(r:ℝ)*D.meanRelativeError hr := by
  have hp := BiasedEnsemble.role_clone_bias_edges_le D.root D.initial D.cycleLaw hr D.uniformCard D.cloneLambda0
  have ha := BiasedEnsemble.clone_average_balance hr D.uniformCard D.root D.initial D.cycleLaw
    (D.k_pos hr) D.cloneLambda0
  have he (i : D.ensembleIndex) :
      (∑ f ∈ (D.ensembleHost hr i).edges,
        |(D.ensembleMatchingLaw hr i).event (fun M => f∈M.val.val)-1/D.cloneLambda0|) =
      ∑ f : ↥(D.ensembleHost hr i).edges,
        |kahnEdgeProbability (D.ensembleMatchingLaw hr i) f-1/D.cloneLambda0| := by
    exact (sum_coe_sort _ _).symm
  change _ ≤ ∑ i, D.ensembleLaw.mass i *
    (∑ f ∈ (D.ensembleHost hr i).edges,
      |(D.ensembleMatchingLaw hr i).event (fun M => f∈M.val.val)-1/D.cloneLambda0|) at hp
  simp_rw [he] at hp
  have hc : ((r*D.k:ℕ):ℝ)/(r:ℝ)=(D.k:ℝ) := by
    rw [Nat.cast_mul,mul_div_cancel_left₀ _ (show (r:ℝ)≠0 by exact_mod_cast (show r≠0 by omega))]
  rw [hc]
  exact hp.trans ha

/-- The finite, quantitative conclusion after the genuine entropy and mean
budgets are supplied. All projection and conditioning steps are proved above. -/
theorem finite_entropy_balance (D : BiasedRoleInstance r) (hr : 3≤r)
    (A C E : ℝ) (hA : 2≤A) (hC : 0≤C) (hCA : C≤A)
    (hE0 : 0≤E) (hE1 : E≤1)
    (hdeg : ∀v,(vertexDegree D.host v:ℝ)≤C*D.μ)
    (hv : ((r*D.k:ℕ):ℝ)≤A*D.N)
    (hL : D.meanLocalDeficit hr+D.meanDegreeDeficit hr≤A*D.N*E)
    (ht : D.meanRelativeError hr≤A*E)
    (hB : D.junctionDeficit hr≤A*D.N*E)
    (hlam : D.μ/A≤D.cloneLambda0) :
    D.deviation≤(4*A+A^2+2*(r:ℝ)*((r:ℝ)-1)*A^3)*D.N*Real.sqrt E := by
  have hμ := D.μ_pos hr
  have hN : (0:ℝ)<D.N := Nat.cast_pos.mpr D.N_pos
  have hrR : (3:ℝ)≤r := by exact_mod_cast hr
  have hA1 : 1≤A := by linarith
  have hlam0 := D.cloneLambda0_pos hr
  have hraw := ConnectedCloneCycle.junctionRole_host_bias D.root D.initial
    (D.cycleLaw.map biasedConnectedCycle) D.host D.uniformCard (C*D.μ)
    (mul_nonneg hC hμ.le) hdeg (junctionFraction r)
    (junctionFraction_pos_lt_one r hr).1 (junctionFraction_pos_lt_one r hr).2
  rw [one_sub_junctionFraction r hr] at hraw
  change roleJunctionDeviation r D.markers D.host D.root D.initial D.cycleLaw ≤
    (r*(r-1):ℕ)*Real.sqrt (4*(D.host.card:ℝ)*(C*D.μ)*D.junctionDeficit hr) at hraw
  have hy : roleJunctionDeviation r D.markers D.host D.root D.initial D.cycleLaw /D.cloneLambda0 ≤
      ((r:ℝ)*((r:ℝ)-1)/D.cloneLambda0)*
        Real.sqrt (4*(D.host.card:ℝ)*(C*D.μ)*D.junctionDeficit hr) := by
    have h := div_le_div_of_nonneg_right hraw hlam0.le
    simpa only [Nat.cast_mul,Nat.cast_sub (show 1≤r by omega),Nat.cast_one,mul_div_right_comm] using h
  have hm : (D.host.card:ℝ)≤A*D.N*D.μ := by
    have he : (D.N:ℝ)*D.μ=(r:ℝ)*D.host.card := by
      unfold μ meanDegree
      simp only [Fintype.card_fin]
      field_simp [hN.ne']
    have hm0 : (0:ℝ)≤D.host.card := Nat.cast_nonneg _
    calc
      (D.host.card:ℝ)≤(D.N:ℝ)*D.μ := by nlinarith
      _ ≤ A*((D.N:ℝ)*D.μ) := by nlinarith [mul_le_mul_of_nonneg_right hA1 (mul_nonneg hN.le hμ.le)]
      _ = _ := by ring
  exact entropy_projection_budget hA1 (by linarith) hN hμ hE0 hE1
    (Nat.cast_nonneg _) (add_nonneg (D.meanLocalDeficit_nonneg hr) (D.meanDegreeDeficit_nonneg hr))
    (D.meanRelativeError_nonneg hr) (mul_nonneg hC hμ.le) (D.junctionDeficit_nonneg hr)
    hv hL ht (mul_le_mul_of_nonneg_right hCA hμ.le) hB hm hlam
    (D.role_clone_deviation_bound hr) hy
    (biasedRoleDeviation_triangle r hr D.markers D.host D.root D.initial D.cycleLaw hμ)

end LooseHamilton.BiasedRoleInstance
