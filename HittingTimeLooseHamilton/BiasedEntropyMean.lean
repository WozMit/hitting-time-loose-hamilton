module

public import HittingTimeLooseHamilton.BiasedCloneMean
public import HittingTimeLooseHamilton.BiasedEntropyEnsemble
public import HittingTimeLooseHamilton.BiasedCloneConditionalDegrees
public import HittingTimeLooseHamilton.BiasedRoleParameters
public import HittingTimeLooseHamilton.BiasedMatchingBalance

public section

noncomputable section
namespace LooseHamilton
open Finset FiniteEntropy
open scoped BigOperators
namespace BiasedEnsemble
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {r : ℕ} {markers G : SimpleHypergraph V}
variable (hr : 3≤r) (hG : ∀e∈G,e.card=r)
variable (root : ↥markers) (a : ↥root.val) (p : Law (BiasedCycleState r markers G))

lemma mean_eq (z : Index root a p) :
    kahnMeanDegree (host hr hG root a p z) =
      ((cloneHost G (biasedCloneUniverse root a (reference root a p z))).card:ℝ)/
        (ordinaryEdgeCount r markers:ℝ) := by
  rw [kahnMeanDegree, host, biasedCloneKahnHost_card]
  have hr0 : (r:ℝ)≠0 := by exact_mod_cast (show r≠0 by omega)
  rw [Nat.cast_mul]
  exact mul_div_mul_left _ _ hr0

end BiasedEnsemble
namespace BiasedRoleInstance
variable {r : ℕ}

@[expose] def cloneLambda0 (D : BiasedRoleInstance r) : ℝ := privateFraction r^(r-2)*D.μ

@[expose] def cloneRelativeConstant (r : ℕ) (C : ℝ) : ℝ :=
  MixedCycleWitness.cloneMeanConstant r C / privateFraction r^(r-2)

lemma cloneLambda0_pos (D : BiasedRoleInstance r) (hr : 3≤r) : 0<D.cloneLambda0 := by
  have hr' : (3:ℝ)≤r := by exact_mod_cast hr
  apply mul_pos _ (D.μ_pos hr)
  apply pow_pos
  unfold privateFraction
  exact div_pos (by linarith) (by linarith)

lemma clone_mean_absolute (D : BiasedRoleInstance r) (hr : 3≤r)
    (hG : ∀e∈D.host,e.card=r) (C δ : ℝ) (hC : 0≤C) (hδ : 0≤δ)
    (hμ : 1≤D.μ) (hdeg : ∀v, (vertexDegree D.host v:ℝ)≤C*D.μ)
    (hs : 2*D.s≤D.N) (hpart : D.partitionBound δ)
    (z : BiasedEnsemble.Index D.root D.initial D.cycleLaw) :
    |kahnMeanDegree (BiasedEnsemble.host hr hG D.root D.initial D.cycleLaw z)-D.cloneLambda0|≤
      MixedCycleWitness.cloneMeanConstant r C*(δ+(D.s:ℝ)/D.N)*D.μ := by
  let Z := BiasedEnsemble.reference D.root D.initial D.cycleLaw z
  let W := (biasedConnectedCycle Z).directedWitness D.root D.initial
  have hk : Z.val.card = D.k := (biasedConnectedCycle Z).property.edge_card hr
  have hA : (univ.image W.junction).card=D.k+D.s := by
    rw [W.junction_card, W.length_eq]
    change D.markers.card+Z.val.card=D.k+D.s
    rw [hk]
    simp [s,Nat.add_comm]
  have hp := hpart (univ.image W.junction) W.marked_vertices_subset_junctions hA
  have ht := W.cloneHost_mean_quantitative D.host hr hG C δ hC hδ hμ hdeg
    (by simpa [s] using hs) (by simpa using D.N_pos) (by simpa [μ] using hp)
  rw [BiasedEnsemble.mean_eq]
  change |((cloneHost D.host W.cloneVertices).card:ℝ)/(D.k:ℝ)-D.cloneLambda0|≤_
  have hk' : (biasedConnectedCycle Z).val.card=D.k := hk
  simpa only [hk', Fintype.card_fin, cloneLambda0, μ, s] using ht

lemma clone_mean_relative (D : BiasedRoleInstance r) (hr : 3≤r)
    (hG : ∀e∈D.host,e.card=r) (C δ : ℝ) (hC : 0≤C) (hδ : 0≤δ)
    (hμ : 1≤D.μ) (hdeg : ∀v, (vertexDegree D.host v:ℝ)≤C*D.μ)
    (hs : 2*D.s≤D.N) (hpart : D.partitionBound δ)
    (z : BiasedEnsemble.Index D.root D.initial D.cycleLaw) :
    |kahnMeanDegree (BiasedEnsemble.host hr hG D.root D.initial D.cycleLaw z)/D.cloneLambda0-1|≤
      cloneRelativeConstant r C*(δ+(D.s:ℝ)/D.N) := by
  have hp := D.cloneLambda0_pos hr
  have hm := D.clone_mean_absolute hr hG C δ hC hδ hμ hdeg hs hpart z
  rw [← div_self (ne_of_gt hp), ← sub_div, abs_div, abs_of_pos hp]
  apply (div_le_iff₀ hp).mpr
  have hb : privateFraction r^(r-2)≠0 := by
    intro hh
    have hz : D.cloneLambda0=0 := by simp [cloneLambda0,hh]
    linarith
  convert hm using 1
  unfold cloneRelativeConstant cloneLambda0
  field_simp
  <;> ring

lemma clone_mean_pos (D : BiasedRoleInstance r) (hr : 3≤r)
    (hG : ∀e∈D.host,e.card=r)
    (z : BiasedEnsemble.Index D.root D.initial D.cycleLaw) :
    0<kahnMeanDegree (BiasedEnsemble.host hr hG D.root D.initial D.cycleLaw z) := by
  apply kahn_mean_degree_pos (BiasedEnsemble.matchingLaw hr hG D.root D.initial D.cycleLaw z)
  exact Nat.mul_pos (by omega) (D.k_pos hr)

lemma clone_mean_log_upper (D : BiasedRoleInstance r) (hr : 3≤r)
    (hG : ∀e∈D.host,e.card=r) (C δ : ℝ) (hC : 0≤C) (hδ : 0≤δ)
    (hμ : 1≤D.μ) (hdeg : ∀v, (vertexDegree D.host v:ℝ)≤C*D.μ)
    (hs : 2*D.s≤D.N) (hpart : D.partitionBound δ)
    (z : BiasedEnsemble.Index D.root D.initial D.cycleLaw) :
    Real.log (kahnMeanDegree (BiasedEnsemble.host hr hG D.root D.initial D.cycleLaw z)) ≤
      Real.log D.cloneLambda0+cloneRelativeConstant r C*(δ+(D.s:ℝ)/D.N) := by
  have hmean := D.clone_mean_pos hr hG z
  have hbase := D.cloneLambda0_pos hr
  have hl := Real.log_le_sub_one_of_pos (div_pos hmean hbase)
  rw [Real.log_div (ne_of_gt hmean) (ne_of_gt hbase)] at hl
  have hb := (abs_le.mp (D.clone_mean_relative hr hG C δ hC hδ hμ hdeg hs hpart z)).2
  linarith
end BiasedRoleInstance
end LooseHamilton
